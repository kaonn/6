structure ExampleLrVals =
  ExampleLrValsFun(structure Token = LrParser.Token)

structure ExampleLex =
  ExampleLexFun(structure Tokens = ExampleLrVals.Tokens)

structure ExampleParser =
  JoinWithArg
    (structure LrParser = LrParser
     structure ParserData = ExampleLrVals.ParserData
     structure Lex = ExampleLex)

structure Example =
struct
  fun stringreader s =
    let
      val pos = ref 0
      val remainder = ref (String.size s)
      fun min(a, b) = if a < b then a else b
    in
      fn n =>
        let
          val m = min(n, !remainder)
          val s = String.substring(s, !pos, m)
          val () = pos := !pos + m
          val () = remainder := !remainder - m
        in
          s
        end
    end

  exception ParseError of Pos.t * string

  fun error fileName (s, pos, pos') : unit =
    raise ParseError (Pos.pos (pos fileName) (pos' fileName), s)

  exception EvalError of string

  local 

    open Abt infix $ infix $$
    open Operator
    fun step abt = 
        let 

          fun sstep M i = 
            case out M of
              ` x => (case Var.name x of
                       SOME n => raise EvalError ("unbound variable " ^  n)
                     | _ => raise EvalError ("unbound variable"))
            | theta $ l =>
               ( case theta of
                  LAM => raise EvalError ("stepped to a value (lambda)")
                | AP => 
                    let val [\([],f), \([],v)] = l 
                    in case out f of
                         LAM $ [\([x], M')] => 
                         let val M'' = substVar (v, x) M'
                         in (M'', i + 1)
                         end
                       | _ => raise EvalError ("applying a non lambda")
                    end
                | RET => 
                    let val [\([],v)] = l in 
                    (M,i)
                    end
                | REC => 
                    let val [\([],v), \([],M0), \([x,f],M1)] = l
                    in case out v of
                         ZERO $ _ => (M0, i+1)
                       | SUC $ [\([],v')] => 
                           let val thunk = THUNK $$ [\([], REC $$ [\([],v'), \([],M0), \([x,f],M1)])] 
                               val M1' = substVar (v',x) M1 
                               val seq = SEQ $$ [\([], thunk), \([f], M1')]
                           in (seq, i+1)
                           end
                       | _ => raise EvalError ("rec'ing on a non nat")
                    end
                | SEQ => 
                    let val [\([],v), \([x],M2)] = l
                    in case out v of
                         THUNK $ [\([],M1)] => 
                          let val (M1',c) = sstep M1 i in 
                          case out M1' of
                            RET $ [\([],r)] => (substVar (r,x) M2, c+1)
                          | _ => (SEQ $$ [\([],THUNK $$ [\([],M1')]), \([x],M2)],
                          i+1)
                          end
                    end
                | _ => raise EvalError "Unimplemented"
                (*
                | NUM => ([mkValence [] NAT], VAL)
                | ZERO => ([], VAL)
                | SUC => ([mkValence [] VAL], VAL)
                | LIT _ => ([], NAT)
                | THUNK => ([mkValence [] COMP], VAL)
                *)
                )
            | _ => raise EvalError ("meta variable found")

          fun steps abt i = 
            let val (M,c) = sstep abt i in 
            case out M of
              RET $ _ => (M,c) 
            | _ => steps M (i+1)
          end

        in
          steps abt 0
        end

   
  in 

  fun loop () =
    let
      val input = (print "> "; TextIO.inputLine TextIO.stdIn)
    in
      case input of
           NONE => 0
         | SOME str =>
             ((let
                 val lexer = ExampleParser.makeLexer (stringreader (Option.valOf input)) "-"
                 val (result, _) = ExampleParser.parse (1, lexer, error "-", "-")
                 val ast as (Ast.$ (theta, es)) = Ast.out result 
                 val (_, tau) = O.arity theta
                 val abt = AstToAbt.convert (Abt.Metavar.Ctx.empty, AstToAbt.NameEnv.empty) (Ast.into ast, tau)
               in
                 let val _ = print (ShowAbt.toString abt ^ "\n\n")
                     val (M,c) = step abt
                 in 
                       print ("evaluated to:\n")
                     ; print (ShowAbt.toString M ^ "\n\n")
                     ; print ("in " ^ Int.toString c ^ " steps\n")
                 end
               end
               handle err => print ("Error: " ^ exnMessage err ^ "\n\n"));
              loop ())
    end

  fun main (name, args) =
    (print "\n\nType an expression at the prompt\n\n";
     loop ())
  end
end

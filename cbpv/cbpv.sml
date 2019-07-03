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

          val stack_depth = ref 0 

          fun ret v = RET $$ [\([],v)]

          fun thunk M = THUNK $$ [\([],M)]

          fun check_node v = 
            case out v of 
              NODE n $ children => (NODE n,children)
            | _ => raise EvalError "matching on non-tree"

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
                    let val _ = stack_depth := Int.max(!stack_depth - 1,0)
                        val [\([],v)] = l in 
                    (M,i)
                    end
                | FST => 
                    let val [\([],v)] = l in 
                      case out v of 
                        PAIR $ [\([],v1),\([],v2)] => (RET $$ [\([],v1)], i+1)
                      | _ => raise EvalError ("proj'ing out of non prod")
                    end
                | SND => 
                    let val [\([],v)] = l in 
                      case out v of 
                        PAIR $ [\([],v1),\([],v2)] => (RET $$ [\([],v2)], i+1)
                      | _ => raise EvalError ("proj'ing out of non prod")
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
                | IF => 
                    let val [\([],v), \([],M0), \([],M1)] = l
                    in case out v of
                         ZERO $ _ => (M1, i+1)
                       | SUC $ _ => (M0, i+1)
                       | _ => raise EvalError ("if'ing on a non nat")
                    end

                | PLUS => 
                    let val [\([],v1),\([],v2)] = l 
                        val LIT n1 $ [] = out v1 
                        val LIT n2 $ [] = out v2 
                        val v = LIT (n1 + n2) $$ [] 
                    in (RET $$ [\([], v)], i+1)
                    end
                | MINUS => 
                    let val [\([],v1),\([],v2)] = l 
                        val LIT n1 $ [] = out v1 
                        val LIT n2 $ [] = out v2 
                        val v = LIT (Int.max(n1 - n2,0)) $$ [] 
                    in (RET $$ [\([], v)], i+1)
                    end
                | GT => 
                    let val [\([],v1),\([],v2)] = l 
                        val LIT n1 $ [] = out v1 
                        val LIT n2 $ [] = out v2 
                        val v = 
                          if n1 > n2 then SUC $$ [\([], ZERO $$ [])]
                          else ZERO $$ [] 
                    in (RET $$ [\([], v)], i+1)
                    end

                | TMATCH => 
                    let val \([],v) = hd l 
                        val (NODE n, children) = check_node v
                    in case n of 
                         LEAF => 
                         let val \([s,d],M) = List.nth (l, 1)
                             val [\([],S),\([],D)] = children
                             val M' = substVar (D,d) (substVar (S,s) M) 
                         in (M', i+1)
                         end
                       | SINGLE => 
                         let val \([s,d,x],M) = List.nth (l, 2)
                             val [\([],S),\([],D),\([],v')] = children 
                             val M' = substVar (D,d) (substVar (S,s) (substVar (v',x) M)) 
                         in (M', i+1)
                         end
                       | T2 => 
                         let val \([s,d,l,r],M) = List.nth (l, 3)
                             val [\([],S),\([],D),\([],c1),\([],c2)] = children 
                             val M' = substVar (D,d) (substVar (S,s) (substVar (c2,r) (substVar (c1,l) M))) 
                         in (M', i+1)
                         end
                       | T3 => 
                         let val \([s,d,l,m,r],M) = List.nth (l, 4)
                             val [\([],S),\([],D),\([],c1),\([],c2),\([],c3)] = children 
                             val M' = substVar (D,d) (substVar (S,s) (substVar (c3,r) (substVar (c2,m)
                             (substVar (c1,l) M)))) 
                         in (M', i+1)
                         end

                    end

                | TREC => 
                    let val _ = stack_depth := !stack_depth + 1
                        val [\([],v), \([],M0), \([x],M1),
                    \([l,r,fl,fr],M2),\([l3,m3,r3,fl3,fm3,fr3],M3)] = l
                        val (NODE n, children) = check_node v
                    in case n of 
                         LEAF => (M0,i+1)
                       | SINGLE => 
                           let val [\([],S),\([],D),\([],v')] = children 
                               val M1' = substVar (v',x) M1 
                           in (M1', i+1)
                           end
                       | T2 =>
                           let val [\([],S),\([],D),\([],c1),\([],c2)] = children 
                               val Fl = THUNK $$ [\([], TREC $$ 
                               [\([],c1), \([],M0), \([x],M1),
                                \([l,r,fl,fr],M2),\([l3,m3,r3,fl3,fm3,fr3],M3)])]
                               val Fr = THUNK $$ [\([], TREC $$ 
                               [\([],c2), \([],M0), \([x],M1),
                                \([l,r,fl,fr],M2),\([l3,m3,r3,fl3,fm3,fr3],M3)])]
                               val M2' = substVar (Fr, fr) (substVar (Fl, fl)
                               (substVar (c2,r) (substVar (c1, l) M2)))
                               (* val ret = RET $$ [\([], THUNK $$ [\([],
                               * M2')])] *)
                           in (M2',i+1)
                           end
                       | T3 =>
                           let val [\([],S),\([],D),\([],c1),\([],c2),\([],c3)] = children 
                               val Fl = THUNK $$ [\([], TREC $$ 
                               [\([],c1), \([],M0), \([x],M1),
                                \([l,r,fl,fr],M2),\([l3,m3,r3,fl3,fm3,fr3],M3)])]
                               val Fm = THUNK $$ [\([], TREC $$ 
                               [\([],c2), \([],M0), \([x],M1),
                                \([l,r,fl,fr],M2),\([l3,m3,r3,fl3,fm3,fr3],M3)])]
                               val Fr = THUNK $$ [\([], TREC $$ 
                               [\([],c3), \([],M0), \([x],M1),
                                \([l,r,fl,fr],M2),\([l3,m3,r3,fl3,fm3,fr3],M3)])]
                               val M3' = substVar (Fr,fr3) (substVar (Fm,fm3)
                                   (substVar (Fl,fl3) (substVar (c3,r3) (substVar (c2,m3)
                                   (substVar (c1, l3) M3)))))
                               (* val ret = RET $$ [\([], THUNK $$ [\([],
                               * M3')])] *)
                           in (M3',i+1)
                           end
                    end
                | SEQ => 
                    let val [\([],v), \([x],M2)] = l
                    in case out v of
                         THUNK $ [\([],M1)] => 
                          (case out M1 of
                            RET $ [\([],r)] => (substVar (r,x) M2, i+1)
                          | _ => 
                          let val (M1',c) = sstep M1 i in 
                          (SEQ $$ [\([],THUNK $$ [\([],M1')]), \([x],M2)],i+1)
                          end)
                      | _ => raise EvalError "seq'ing non-thunk"
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

          fun steps abt i  = 
            let val (M,c) = sstep abt i 
            handle EvalError msg => (print msg ; raise Fail "eval error")
                val _ = print ("step " ^ Int.toString i ^ ": stack_depth " ^
                Int.toString (!stack_depth) ^ "\n") 
                val _ = print (implode (List.tabulate (!stack_depth, fn _ => #"#")))
                val _ = print (ShowAbt.toString M ^ "\n\n")
            in 
            case out M of
              RET $ _ => (M,c-1) 
            | _ => steps M (i+1)
             
          end


        in
          steps abt 1
        end

   
  in 

  fun loadFile input = 
    if String.isPrefix "load" input then
      let val str = TextIO.openIn ("cbpv/" ^ Option.valOf (
        String.fromString (String.extract (input, 5, NONE))))
      in 
        TextIO.inputAll str
      end
    else 
      input

  fun printTree M = 
    let fun f n =
    case out n of 
      NODE n $ children =>
          (case n of 
            LEAF => "*"
          | SINGLE => 
              let val [_,_,\([],x)] = children in 
                ShowAbt.toString x
              end
          | T2 => 
              let val [_,_,\([],c1), \([],c2)] = children in 
                "(" ^ f c1 ^ "," ^ f c2 ^ ")"
              end
          | T3 => 
              let val [_,_,\([],c1), \([],c2), \([],c3)] = children in 
                "(" ^ f c1 ^ "," ^ f c2 ^ "," ^ f c3 ^ ")"
              end)
    | _ => raise Fail "info: return value not a tree\n"
    in f M
    end

  fun printAbt M = 
    let fun f n = 
      case out n of
        ZERO $ [] => Int.toString 0
      | SUC $ [\([],n')] => Int.toString (1 + (Option.valOf o Int.fromString) (f n'))
      | PAIR $ [\([],v1),\([],v2)] => 
          "(" ^ (f v1) ^ ", " ^ (f v2) ^ ")"
      | _ => raise Fail "info: return value not a nat tuple\n"
    in 
      case out M of
        RET $ [\([],n)] => 
        (printTree n handle Fail msg =>
          (let val _ = print msg in 
          (f n handle Fail msg =>
          let val _ = print msg in 
          ShowAbt.toString M 
          end)
          end))
      | _ => raise Fail ("impossible state: " ^  ShowAbt.toString M)
    end

  fun loop () =
    let
      val input = (print "> "; TextIO.inputLine TextIO.stdIn)
    in
      case input of
           NONE => 0
         | SOME str =>
             ((let
                 val file = loadFile str 
                 val lexer = ExampleParser.makeLexer (stringreader file) "-"
                 val (result, _) = ExampleParser.parse (1, lexer, error "-", "-")
                 val ast as (Ast.$ (theta, es)) = Ast.out result 
                 val (_, tau) = O.arity theta
                 val abt = AstToAbt.convert (Abt.Metavar.Ctx.empty, AstToAbt.NameEnv.empty) (Ast.into ast, tau)
               in
                 let val _ = print (ShowAbt.toString abt ^ "\n\n")
                     val (M,c) = step abt
                     val str = printAbt M
                 in 
                       print ("evaluated to:\n")
                     ; print (str ^ "\n\n")
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

structure Sort =
struct
  datatype t = VAL | NAT | COMP
  val eq : t * t -> bool = op=
  fun toString VAL = "val"
    | toString NAT = "nat"
    | toString COMP = "comp"
end

structure O =
struct
  structure Ar = ListAbtArity (structure S = Sort)
  datatype node = LEAF | SINGLE | T2 | T3 
  datatype t = LAM | AP | LIT of int | THUNK | RET | REC | SEQ | ZERO |
  SUC | PLUS | MINUS | TREC | TMATCH | NODE of node 
  | PAIR | FST | SND | GT


  val eq : t * t -> bool = op=
  val toString =
    fn LAM => "lam"
     | AP => "ap"
     | LIT n => Int.toString n
     | THUNK => "thunk"
     | RET => "ret"
     | REC => "rec"
     | SEQ => "seq"
     | ZERO => "zero"
     | SUC => "suc"
     | PLUS => "+" 
     | MINUS => "-" 
     | TREC => "trec"
     | TMATCH => "tmatch"
     | NODE n => 
         (case n of 
           LEAF => "leaf" 
         | SINGLE => "single"
         | T2 => "t2" 
         | T3 => "t3") 
     | PAIR => "pair"
     | FST => "fst"
     | SND => "snd"
     | GT => ">"

  local
    open Sort
    fun mkValence q s = (q, s)
  in
    val arity =
      fn LAM => ([mkValence [VAL] COMP], VAL)
      | AP => ([mkValence [] VAL, mkValence [] VAL], COMP)
      | ZERO => ([], VAL)
      | SUC => ([mkValence [] VAL], VAL)
      | LIT _ => ([], VAL)
      | RET => ([mkValence [] VAL], COMP)
      | REC => ([mkValence [] VAL, mkValence [] COMP, mkValence [VAL,VAL] COMP], COMP)
      | THUNK => ([mkValence [] COMP], VAL)
      | SEQ => ([mkValence [] VAL, mkValence [VAL] COMP],COMP)
      | PLUS => ([mkValence [] VAL, mkValence [] VAL],COMP)
      | MINUS => ([mkValence [] VAL, mkValence [] VAL],COMP)
      | GT => ([mkValence [] VAL, mkValence [] VAL],COMP)
      | NODE n =>
          (case n of
           LEAF => ([mkValence [] VAL, mkValence [] VAL], VAL)
         | SINGLE => ([mkValence [] VAL,mkValence [] VAL, mkValence [] VAL], VAL)
         | T2 => ([mkValence [] VAL, mkValence [] VAL,mkValence [] VAL, mkValence [] VAL], VAL)
         | T3 => ([mkValence [] VAL, mkValence [] VAL, mkValence [] VAL,mkValence [] VAL, mkValence [] VAL], VAL))
      | FST => ([mkValence [] VAL], COMP)
      | SND => ([mkValence [] VAL], COMP)
      | PAIR => ([mkValence [] VAL, mkValence [] VAL], VAL)
      | TREC => ([mkValence [] VAL, 
        mkValence [] COMP, 
        mkValence [VAL] COMP,
        mkValence [VAL,VAL,VAL,VAL] COMP,
        mkValence [VAL,VAL,VAL,VAL,VAL,VAL] COMP],
        COMP)
      | TMATCH => ([mkValence [] VAL, 
        mkValence [VAL,VAL] COMP, 
        mkValence [VAL,VAL,VAL] COMP,
        mkValence [VAL,VAL,VAL,VAL] COMP,
        mkValence [VAL,VAL,VAL,VAL,VAL] COMP],
        COMP)

  end
end


structure Operator = O

structure AbtKit =
struct
  structure O = Operator
    and Metavar = AbtSymbol ()
    and Var = AbtSymbol ()
  type annotation = Pos.t
end

structure Abt = Abt (AbtKit)
structure ShowAbt = DebugShowAbt (Abt)

structure AstKit =
struct
  structure Operator = Operator
  structure Metavar = AbtSymbol()
  type annotation = Pos.t
end

structure Ast = AstUtil (Ast (AstKit))
structure AstToAbt = AstToAbt (structure Abt = Abt and Ast = Ast)


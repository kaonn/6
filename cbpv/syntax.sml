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
  datatype t = LAM | AP | NUM | LIT of int | THUNK | RET | REC | SEQ | ZERO |
  SUC 

  val eq : t * t -> bool = op=
  val toString =
    fn LAM => "lam"
     | AP => "ap"
     | NUM => "num"
     | LIT n => Int.toString n
     | THUNK => "thunk"
     | RET => "ret"
     | REC => "rec"
     | SEQ => "seq"
     | ZERO => "zero"
     | SUC => "suc"

  local
    open Sort
    fun mkValence q s = (q, s)
  in
    val arity =
      fn LAM => ([mkValence [VAL] COMP], VAL)
      | AP => ([mkValence [] VAL, mkValence [] VAL], COMP)
      | NUM => ([mkValence [] NAT], VAL)
      | ZERO => ([], VAL)
      | SUC => ([mkValence [] VAL], VAL)
      | LIT _ => ([], NAT)
      | RET => ([mkValence [] VAL], COMP)
      | REC => ([mkValence [] VAL, mkValence [] COMP, mkValence [VAL,VAL] COMP], COMP)
      | THUNK => ([mkValence [] COMP], VAL)
      | SEQ => ([mkValence [] VAL, mkValence [VAL] COMP],COMP)
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


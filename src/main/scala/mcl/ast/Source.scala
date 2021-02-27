package mcl.ast

import mcl.Sym

object Source with
  enum Term with
    case Type(level: Int)
    case Fun(id: Sym, domain: Term, codomain: Term)
    case Abs(id: Sym, domain: Term, body: Term)
    case App(operator: Term, operand: Term)
    case Var(id: Sym)
    case Ind(id: Sym, constructors: Seq[Sym], body: Term)

package mcl.ast

object Typed with
  enum Term(val typ: () => Term) with
    case Prop(t: () => Term) extends Term(t)
    case Type(level: Int, t: () => Term) extends Term(t)
    case Fun(id: Int, domain: Term, codomain: Term, t: () => Term) extends Term(t)
    case Abs(id: Int, body: Term, t: () => Term) extends Term(t)
    case App(operator: Term, operand: Term, t: () => Term) extends Term(t)
    case Var(id: Int, t: () => Term) extends Term(t)

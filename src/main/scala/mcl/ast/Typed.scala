package mcl.ast

object Typed with
  enum Term(val typ: Source.Term) with
    case Prop(t: Source.Term) extends Term(t)
    case Type(level: Int, t: Source.Term) extends Term(t)
    case Fun(id: Int, domain: Term, codomain: Term, t: Source.Term) extends Term(t)
    case Abs(id: Int, body: Term, t: Source.Term) extends Term(t)
    case App(operator: Term, operand: Term, t: Source.Term) extends Term(t)
    case Var(id: Int, t: Source.Term) extends Term(t)

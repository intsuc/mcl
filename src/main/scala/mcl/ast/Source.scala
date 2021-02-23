package mcl.ast

object Source with
  enum Term with
    case Prop
    case Type(level: Int)
    case Fun(id: Int, domain: Term, codomain: Term)
    case Abs(id: Int, body: Term)
    case App(operator: Term, operand: Term)
    case Var(id: Int)
    case Anno(target: Term, annotation: Term)

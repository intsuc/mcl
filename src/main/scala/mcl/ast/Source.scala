package mcl.ast

object Source with
  enum Term with
    case Type(level: Int)
    case Fun(id: Int, domain: Term, codomain: Term)
    case Abs(id: Int, domain: Term, body: Term)
    case App(operator: Term, operand: Term)
    case Var(id: Int)
    case Ind(id: Int, constructors: Seq[Int], body: Term)

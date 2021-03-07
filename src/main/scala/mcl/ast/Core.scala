package mcl.ast

import Indices.Idx

object Core with
  enum Exp with
    case Typ(level: Int)
    case Fun(domain: Exp, codomain: Exp)
    case Abs(domain: Exp, body: Exp)
    case App(operator: Exp, operand: Exp)
    case Var(idx: Idx)

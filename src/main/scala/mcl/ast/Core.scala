package mcl.ast

import Indices.Idx

// TODO: eliminator for sum types
object Core with
  enum Exp with
    case Typ(level: Int)
    case Fun(domain: Exp, codomain: Exp)
    case Abs(domain: Exp, body: Exp)
    case App(operator: Exp, operand: Exp)
    case Sum(variants: Seq[Exp])
    case Inj(annotation: Exp, index: Int, target: Exp)
    case Var(idx: Idx)

package mcl.ast

import Indices.Idx

// TODO: eliminator for sum types
object Core with
  enum Exp with
    case Typ(level: Int)
    case Fun(domain: Exp, codomain: Exp)
    case Abs(body: Exp)
    case App(operator: Exp, operand: Exp)
    case Sum(variants: Seq[Exp])
    case Inj(index: Int, target: Exp)
    case Var(idx: Idx)
    case Ann(target: Exp, annotation: Exp)

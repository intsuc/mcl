package mcl.ast

import mcl.Sym

// TODO: pattern matching
object Source with
  enum Exp with
    case Type(level: Int)
    case Fun(id: Sym, domain: Exp, codomain: Exp)
    case Abs(id: Sym, domain: Exp, body: Exp)
    case App(operator: Exp, operand: Exp)
    case Var(id: Sym)
    case Ind(id: Sym, arity: Exp, constructors: Seq[(Sym, Exp)], body: Exp)

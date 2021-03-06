package mcl.phase

import mcl.Sym
import mcl.ast.Source.Exp

object Type extends (Exp => Option[Exp]):
  private enum Sem with
    case Type(level: Int)
    case Fun(domain: Sem, fun: Sem => Sem)
    case Abs(domain: Sem, abs: Sem => Sem)
    case App(operator: Sem, operand: Sem)
    case Var(id: Sym)

  private def reflect(exp: Exp, env: Map[Sym, Sem] = Map.empty): Sem = exp match
    case Exp.Type(level) =>
      Sem.Type(level)

    case Exp.Fun(id, domain, codomain) =>
      Sem.Fun(reflect(domain, env), sem => reflect(codomain, env + (id -> sem)))

    case Exp.Abs(id, domain, body) =>
      Sem.Abs(reflect(domain, env), sem => reflect(body, env + (id -> sem)))

    case Exp.App(operator, operand) =>
      (reflect(operator, env), reflect(operand, env)) match
      case (Sem.Abs(_, abs), operand) => abs(operand)
      case (operator, operand) => Sem.App(operator, operand)

    case Exp.Var(id) =>
      env(id)

  private def reify(sem: Sem): Exp = sem match
    case Sem.Type(level) =>
      Exp.Type(level)

    case Sem.Fun(domain, fun) =>
      val id = Sym.fresh()
      Exp.Abs(id, reify(domain), reify(fun(Sem.Var(id))))

    case Sem.Abs(domain, abs) =>
      val id = Sym.fresh()
      Exp.Abs(id, reify(domain), reify(abs(Sem.Var(id))))

    case Sem.App(operator, operand) =>
      Exp.App(reify(operator), reify(operand))

    case Sem.Var(id) =>
      Exp.Var(id)

  extension (sem1: Sem) private def === (sem2: Sem): Boolean = (sem1, sem2) match
    case (Sem.Type(level1), Sem.Type(level2)) =>
      level1 == level2

    case (Sem.Fun(domain1, fun1), Sem.Fun(domain2, fun2)) =>
      domain1 === domain2 && {
        val dummy = Sem.Var(Sym.fresh())
        fun1(dummy) === fun2(dummy)
      }

    case (Sem.Abs(domain1, abs1), Sem.Abs(domain2, abs2)) =>
      domain1 === domain2 && {
        val dummy = Sem.Var(Sym.fresh())
        abs1(dummy) === abs2(dummy)
      }

    case (Sem.App(operator1, operand1), Sem.App(operator2, operand2)) =>
      operator1 === operator2 && operand1 === operand2

    case (Sem.Var(id1), Sem.Var(id2)) =>
      id1 == id2

    case _ =>
      false

  private type Typ = Sem

  private def inferType(exp: Exp)(using Map[Sym, Typ]): Option[Typ] =
    for
      typ <- infer(exp)
      result @ Sem.Type(_) = typ
    yield result

  private def inferFun(exp: Exp)(using Map[Sym, Typ]): Option[Typ] =
    for
      typ <- infer(exp)
      result @ Sem.Fun(_, _) = typ
    yield result

  private def infer(exp: Exp)(using ctx: Map[Sym, Typ]): Option[Typ] = exp match
    case Exp.Type(level) =>
      Some(Sem.Type(level + 1))

    case Exp.Fun(id, domain, codomain) =>
      for
        Sem.Type(domainLevel) <- inferType(domain)
        Sem.Type(codomainLevel) <- inferType(codomain)(using ctx + (id -> reflect(domain)))
      yield Sem.Type(domainLevel max codomainLevel)

    case Exp.Abs(id, domain, body) =>
      for
        _ <- inferType(domain)
        domain <- Some(reflect(domain))
        codomain <- infer(body)(using ctx + (id -> domain))
      yield Sem.Fun(domain, sem => reflect(reify(codomain), Map(id -> sem)))

    case Exp.App(operator, operand) =>
      for
        Sem.Fun(domain, abs) <- inferFun(operator)
        _ <- check(operand, domain)
      yield abs(reflect(operand))

    case Exp.Var(id) =>
      ctx.get(id)

    // TODO: consistency
    // TODO: positivity
    case Exp.Ind(id, arity, constructors, body) =>
      def result(typ: Exp): Exp = typ match
        case Exp.Fun(_, _, codomain) => result(codomain)
        case typ => typ

      for
        _ <- inferType(arity)
        universe @ Sem.Type(_) = reflect(result(arity))
        arity <- Some(reflect(arity))
        if constructors.forall((_, typ) => check(result(typ), universe)(using ctx + (id -> arity)).isDefined)
        typ <- infer(body)(using ctx + (id -> arity) ++ constructors.map(_ -> reflect(_)))
      yield typ

  // TODO: more checking rules
  private def check(exp: Exp, typ: Typ)(using Map[Sym, Typ]): Option[Unit] =
    for t <- infer(exp) if t === typ yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- infer(exp)(using Map.empty) yield exp

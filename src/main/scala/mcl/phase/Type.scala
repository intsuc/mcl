package mcl.phase

import mcl.Sym
import mcl.ast.Source.Exp

object Type extends (Exp => Option[Exp]):
  private enum Sem with
    case Type(level: Int)
    case Abs(domain: Sem, abs: Sem => Sem, typ: Boolean)
    case Acc(head: Exp, tail: Seq[Sem] = Seq.empty)

  extension (operator: Sem) private def apply(operand: Sem): Sem = operator match
    case Sem.Abs(_, abs, _) =>
      abs(operand)

    case Sem.Acc(head, tail) =>
      Sem.Acc(head, tail :+ operand)

    case _ =>
      throw IllegalStateException()

  private def reflect(exp: Exp, env: Map[Sym, Sem] = Map.empty): Sem = exp match
    case Exp.Type(level) =>
      Sem.Type(level)

    case Exp.Fun(id, domain, codomain) =>
      Sem.Abs(reflect(domain, env), sem => reflect(codomain, env + (id -> sem)), true)

    case Exp.Abs(id, domain, body) =>
      Sem.Abs(reflect(domain, env), sem => reflect(body, env + (id -> sem)), false)

    case Exp.App(operator, operand) =>
      reflect(operator, env)(reflect(operand, env))

    case Exp.Var(id) if env contains id =>
      env(id)

    case exp =>
      Sem.Acc(exp)

  private def reify(sem: Sem): Exp = sem match
    case Sem.Type(level) =>
      Exp.Type(level)

    case Sem.Abs(domain, abs, typ) =>
      val id = Sym.fresh()
      val constructor = if typ then Exp.Fun.apply else Exp.Abs.apply
      constructor(id, reify(domain), reify(abs(Sem.Acc(Exp.Var(id)))))

    case Sem.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => Exp.App(operator, reify(operand)))

  extension (sem1: Sem) private def === (sem2: Sem): Boolean = (sem1, sem2) match
    case (Sem.Abs(domain1, abs1, typ1), Sem.Abs(domain2, abs2, typ2)) if typ1 == typ2 =>
      domain1 === domain2 && {
        val dummy = Sem.Acc(Exp.Var(Sym.fresh()))
        abs1(dummy) === abs2(dummy)
      }

    case (Sem.Acc(head1, tail1), Sem.Acc(head2, tail2)) =>
      head1 == head2 && (tail1 zip tail2).forall(_ === _)

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
      result @ Sem.Abs(_, _, true) = typ
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
      yield Sem.Abs(domain, sem => reflect(reify(codomain), Map(id -> sem)), true)

    case Exp.App(operator, operand) =>
      for
        fun @ Sem.Abs(domain, _, true) <- inferFun(operator)
        _ <- check(operand, domain)
      yield fun(reflect(operand))

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

  private def check(exp: Exp, typ: Typ)(using Map[Sym, Typ]): Option[Unit] =
    for typ1 <- infer(exp) if typ1 === typ yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- infer(exp)(using Map.empty) yield exp

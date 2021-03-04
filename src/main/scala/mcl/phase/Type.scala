package mcl.phase

import mcl.Sym
import mcl.ast.Source.Exp

object Type extends (Exp => Option[Exp]):
  private enum Sem with
    case Type(level: Int)
    case Fun(domain: Sem, fum: Sem => Sem)
    case Abs(domain: Sem, abs: Sem => Sem)
    case Acc(head: Exp, tail: Seq[Sem] = Seq.empty)

  extension (operator: Sem) private def apply(operand: Sem): Sem = operator match
    case Sem.Fun(_, fun) =>
      fun(operand)

    case Sem.Abs(_, abs) =>
      abs(operand)

    case Sem.Acc(head, tail) =>
      Sem.Acc(head, tail :+ operand)

    case _ =>
      throw IllegalStateException()

  private def reflect(exp: Exp, ctx: Map[Sym, Sem] = Map.empty): Sem = exp match
    case Exp.Type(level) =>
      Sem.Type(level)

    case Exp.Fun(id, domain, codomain) =>
      Sem.Fun(reflect(domain, ctx), sem => reflect(codomain, ctx + (id -> sem)))

    case Exp.Abs(id, domain, body) =>
      Sem.Abs(reflect(domain, ctx), sem => reflect(body, ctx + (id -> sem)))

    case Exp.App(operator, operand) =>
      reflect(operator, ctx)(reflect(operand, ctx))

    case Exp.Var(id) if ctx contains id =>
      ctx(id)

    case exp =>
      Sem.Acc(exp)

  private def reify(sem: Sem): Exp = sem match
    case Sem.Type(level) =>
      Exp.Type(level)

    case Sem.Fun(domain, abstraction) =>
      val id = Sym.fresh()
      Exp.Fun(id, reify(domain), reify(abstraction(Sem.Acc(Exp.Var(id)))))

    case Sem.Abs(domain, abstraction) =>
      val id = Sym.fresh()
      Exp.Abs(id, reify(domain), reify(abstraction(Sem.Acc(Exp.Var(id)))))

    case Sem.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => Exp.App(operator, reify(operand)))

  extension (sem1: Sem) private def === (sem2: Sem): Boolean = (sem1, sem2) match
    case (Sem.Fun(domain1, fun1), Sem.Fun(domain2, fun2)) =>
      domain1 === domain2 && {
        val dummy = Sem.Acc(Exp.Var(Sym.fresh()))
        fun1(dummy) === fun2(dummy)
      }

    case (Sem.Abs(domain1, abs1), Sem.Abs(domain2, abs2)) =>
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
        codomain <- infer(body)(using ctx + (id -> reflect(domain)))
      yield reflect(Exp.Fun(id, domain, reify(codomain)))

    case Exp.App(operator, operand) =>
      for
        fun @ Sem.Fun(domain, _) <- inferFun(operator)
        _ <- check(operand, domain)
      yield fun(reflect(operand))

    case Exp.Var(id) =>
      ctx.get(id)

    case Exp.Ind(id, arity, constructors, body) =>
      ??? // TODO

  private def check(exp: Exp, typ: Typ)(using Map[Sym, Typ]): Option[Unit] =
    for typ1 <- infer(exp) if typ1 === typ yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- infer(exp)(using Map.empty) yield exp

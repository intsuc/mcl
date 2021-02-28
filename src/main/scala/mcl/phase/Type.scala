package mcl.phase

import mcl.Sym
import mcl.ast.Source as S

object Type extends (S.Exp => Option[S.Exp]):
  private enum Sem with
    case Abs(domain: Sem, abstraction: Sem => Sem, constructor: (Sym, S.Exp, S.Exp) => S.Exp)
    case Acc(head: S.Exp, tail: Seq[Sem] = Seq.empty)

  extension (sem1: Sem) private def === (sem2: Sem): Boolean = (sem1, sem2) match
    case (Sem.Abs(domain1, abstraction1, constructor1), Sem.Abs(domain2, abstraction2, constructor2)) =>
      constructor1 == constructor2 && domain1 === domain2 && {
        val dummy = Sem.Acc(S.Exp.Var(Sym.fresh()))
        abstraction1(dummy) === abstraction2(dummy)
      }

    case (Sem.Acc(head1, tail1), Sem.Acc(head2, tail2)) =>
      head1 == head2 && (tail1 zip tail2).forall(_ === _)

    case _ =>
      false

  extension (operator: S.Exp) private def apply(operand: S.Exp): Sem = reflect(operator) match
    case Sem.Abs(_, abstraction, _) =>
      abstraction(reflect(operand))

    case Sem.Acc(head, tail) =>
      Sem.Acc(head, tail :+ reflect(operand))

  private val constructorFun = S.Exp.Fun.apply
  private val constructorAbs = S.Exp.Abs.apply

  private def reflect(exp: S.Exp)(using ctx: Map[Sym, Sem] = Map.empty): Sem = exp match
    case S.Exp.Fun(id, domain, codomain) =>
      Sem.Abs(reflect(domain), sem => reflect(codomain)(using ctx + (id -> sem)), constructorFun)

    case S.Exp.Abs(id, domain, body) =>
      Sem.Abs(reflect(domain), sem => reflect(body)(using ctx + (id -> sem)), constructorAbs)

    case S.Exp.App(operator, operand) =>
      operator(operand)

    case S.Exp.Var(id) if ctx contains id =>
      ctx(id)

    case exp =>
      Sem.Acc(exp)

  private def reify(sem: Sem): S.Exp = sem match
    case Sem.Abs(domain, abstraction, reifier) =>
      val id = Sym.fresh()
      reifier(id, reify(domain), reify(abstraction(Sem.Acc(S.Exp.Var(id)))))

    case Sem.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => S.Exp.App(operator, reify(operand)))

  private def normalize(exp: S.Exp): S.Exp = (reify compose reflect)(exp)

  private def inferType(exp: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[S.Exp] =
    for
      typ <- infer(exp)
      result @ S.Exp.Type(_) = normalize(typ)
    yield result

  private def inferFun(exp: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[S.Exp] =
    for
      typ <- infer(exp)
      result @ S.Exp.Fun(_, _, _) = normalize(typ)
    yield result

  private def infer(exp: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[S.Exp] = exp match
    case S.Exp.Type(level) =>
      Some(S.Exp.Type(level + 1))

    case S.Exp.Fun(id, domain, codomain) =>
      for
        S.Exp.Type(domainLevel) <- inferType(domain)
        S.Exp.Type(codomainLevel) <- inferType(codomain)(using ctx + (id -> domain))
      yield S.Exp.Type(domainLevel max codomainLevel)

    case S.Exp.Abs(id, domain, body) =>
      for
        _ <- inferType(domain)
        codomain <- infer(body)(using ctx + (id -> domain))
      yield S.Exp.Fun(id, domain, codomain)

    case S.Exp.App(operator, operand) =>
      for
        fun @ S.Exp.Fun(_, domain, _) <- inferFun(operator)
        if check(operand, domain)
      yield reify(fun(operand))

    case S.Exp.Var(id) =>
      ctx.get(id)

    case S.Exp.Ind(id, constructors, body) =>
      infer(body)(using ctx + (id -> S.Exp.Type(0)) ++ constructors.map(_ -> S.Exp.Var(id)))

  private def check(exp: S.Exp, typ: S.Exp)(using ctx: Map[Sym, S.Exp]): Boolean =
    infer(exp).map(reflect(_) === reflect(typ)).getOrElse(false)

  def apply(exp: S.Exp): Option[S.Exp] =
    for _ <- infer(exp)(using Map.empty) yield exp

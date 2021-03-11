package mcl.phase

import mcl.ast.Core.Exp
import mcl.ast.Indices.*
import Levels.*

object Type extends (Exp => Option[Exp]):
  private type Env = Vector[Sem]

  private final case class Clo(env: Env, body: Exp) with
    def apply(operand: Sem): Sem = reflect(operand +: env, body)

  private enum Sem with
    case Typ(level: Int)
    case Fun(domain: Sem, clo: Clo)
    case Abs(domain: Sem, clo: Clo)
    case App(operator: Sem, operand: Sem)
    case Sum(variants: Seq[Sem])
    case Inj(annotation: Sem, index: Int, target: Sem)
    case Var(lvl: Lvl)

  private def reflect(env: Env, exp: Exp): Sem = exp match
    case Exp.Typ(level) =>
      Sem.Typ(level)

    case Exp.Fun(domain, codomain) =>
      Sem.Fun(reflect(env, domain), Clo(env, codomain))

    case Exp.Abs(domain, body) =>
      Sem.Abs(reflect(env, domain), Clo(env, body))

    case Exp.App(operator, operand) => (reflect(env, operator), reflect(env, operand)) match
      case (Sem.Abs(_, clo), operand) => clo(operand)
      case (operator, operand) => Sem.App(operator, operand)

    case Exp.Sum(variants) =>
      Sem.Sum(variants.map(reflect(env, _)))

    case Exp.Inj(annotation, index, target) =>
      Sem.Inj(reflect(env, annotation), index, reflect(env, target))

    case Exp.Var(idx) =>
      env(idx.toInt)

  private def reify(env: Lvl, sem: Sem): Exp = sem match
    case Sem.Typ(level) =>
      Exp.Typ(level)

    case Sem.Fun(domain, clo) =>
      Exp.Fun(reify(env, domain), reify(env.next, clo(Sem.Var(env))))

    case Sem.Abs(domain, clo) =>
      Exp.Abs(reify(env, domain), reify(env.next, clo(Sem.Var(env))))

    case Sem.App(operator, operand) =>
      Exp.App(reify(env, operator), reify(env, operand))

    case Sem.Sum(variants) =>
      Exp.Sum(variants.map(reify(env, _)))

    case Sem.Inj(annotation, index, target) =>
      Exp.Inj(reify(env, annotation), index, reify(env, target))

    case Sem.Var(lvl) =>
      Exp.Var(lvl.toIdx(env))

  private def conv(env: Lvl, sem1: Sem, sem2: Sem): Boolean = (sem1, sem2) match
    case (Sem.Typ(level1), Sem.Typ(level2)) =>
      level1 == level2

    case (Sem.Fun(domain1, clo1), Sem.Fun(domain2, clo2)) =>
      conv(env, domain1, domain2) && conv(env.next, clo1(Sem.Var(env)), clo2(Sem.Var(env)))

    case (Sem.Abs(domain1, clo1), Sem.Abs(domain2, clo2)) =>
      conv(env, domain1, domain2) && conv(env.next, clo1(Sem.Var(env)), clo2(Sem.Var(env)))

    case (Sem.App(operator1, operand1), Sem.App(operator2, operand2)) =>
      conv(env, operator1, operator2) && conv(env, operand1, operand2)

    case (Sem.Sum(variants1), Sem.Sum(variants2)) =>
      (variants1 zip variants2).forall(conv(env, _, _))

    case (Sem.Inj(annotation1, index1, target1), Sem.Inj(annotation2, index2, target2)) =>
      index1 == index2 && conv(env, annotation1, annotation2) && conv(env, target1, target2)

    case (Sem.Var(lvl1), Sem.Var(lvl2)) =>
      lvl1 == lvl2

    case _ =>
      false

  private type Typ = Sem

  private final case class Ctx(sems: Env, typs: Vector[Typ]) with
    def size: Int = sems.size

  private object Ctx with
    def empty: Ctx = Ctx(Vector.empty, Vector.empty)

  extension (typ: Typ) private def +: (ctx: Ctx): Ctx =
    Ctx(Sem.Var(Lvl(ctx.size)) +: ctx.sems, typ +: ctx.typs)

  private def inferTyp(ctx: Ctx, exp: Exp): Option[Int] =
    for Sem.Typ(level) <- infer(ctx, exp) yield level

  private def infer(ctx: Ctx, exp: Exp): Option[Typ] = exp match
    case Exp.Typ(level) =>
      Some(Sem.Typ(level + 1))

    case Exp.Fun(domain, codomain) =>
      for
        domainLevel <- inferTyp(ctx, domain)
        codomainLevel <- inferTyp(reflect(ctx.sems, domain) +: ctx, codomain)
      yield Sem.Typ(domainLevel max codomainLevel)

    case Exp.Abs(domain, body) =>
      for
        _ <- inferTyp(ctx, domain)
        domain <- Some(reflect(ctx.sems, domain))
        body <- infer(domain +: ctx, body)
      yield Sem.Fun(domain, Clo(ctx.sems, reify(Lvl(ctx.size), body)))

    case Exp.App(operator, operand) =>
      for
        Sem.Fun(domain, clo) <- infer(ctx, operator)
        _ <- check(ctx, operand, domain)
      yield clo(reflect(ctx.sems, operand))

    case Exp.Sum(variants) =>
      val levels = for
        variant <- variants
        level <- inferTyp(ctx, variant)
      yield level
      for
        maxLevel <- levels.maxOption
      yield Sem.Typ(maxLevel)

    case Exp.Inj(annotation, index, target) =>
      for
        _ <- inferTyp(ctx, annotation)
        typ @ Sem.Sum(variants) = reflect(ctx.sems, annotation)
        variant <- variants.lift(index)
        _ <- check(ctx, target, variant)
      yield typ

    case Exp.Var(idx) =>
      Some(ctx.typs(idx.toInt))

  private def check(ctx: Ctx, exp: Exp, typ: Typ): Option[Unit] =
    for t <- infer(ctx, exp) if conv(Lvl(ctx.size), t, typ) yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- infer(Ctx.empty, exp) yield exp

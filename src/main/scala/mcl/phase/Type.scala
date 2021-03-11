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
    case Abs(clo: Clo)
    case App(operator: Sem, operand: Sem)
    case Sum(variants: Seq[Sem])
    case Inj(index: Int, target: Sem)
    case Var(lvl: Lvl)

  private def reflect(env: Env, exp: Exp): Sem = exp match
    case Exp.Typ(level) =>
      Sem.Typ(level)

    case Exp.Fun(domain, codomain) =>
      Sem.Fun(reflect(env, domain), Clo(env, codomain))

    case Exp.Abs(body) =>
      Sem.Abs(Clo(env, body))

    case Exp.App(operator, operand) => (reflect(env, operator), reflect(env, operand)) match
      case (Sem.Abs(clo), operand) => clo(operand)
      case (operator, operand) => Sem.App(operator, operand)

    case Exp.Sum(variants) =>
      Sem.Sum(variants.map(reflect(env, _)))

    case Exp.Inj(index, target) =>
      Sem.Inj(index, reflect(env, target))

    case Exp.Var(idx) =>
      env(idx.toInt)

    case Exp.Ann(target, _) =>
      reflect(env, target)

  private def reify(env: Lvl, sem: Sem): Exp = sem match
    case Sem.Typ(level) =>
      Exp.Typ(level)

    case Sem.Fun(domain, clo) =>
      Exp.Fun(reify(env, domain), reify(env.next, clo(Sem.Var(env))))

    case Sem.Abs(clo) =>
      Exp.Abs(reify(env.next, clo(Sem.Var(env))))

    case Sem.App(operator, operand) =>
      Exp.App(reify(env, operator), reify(env, operand))

    case Sem.Sum(variants) =>
      Exp.Sum(variants.map(reify(env, _)))

    case Sem.Inj(index, target) =>
      Exp.Inj(index, reify(env, target))

    case Sem.Var(lvl) =>
      Exp.Var(lvl.toIdx(env))

  private def conv(env: Lvl, sem1: Sem, sem2: Sem): Boolean = (sem1, sem2) match
    case (Sem.Typ(level1), Sem.Typ(level2)) =>
      level1 == level2

    case (Sem.Fun(domain1, clo1), Sem.Fun(domain2, clo2)) =>
      conv(env, domain1, domain2) && conv(env.next, clo1(Sem.Var(env)), clo2(Sem.Var(env)))

    case (Sem.Abs(clo1), Sem.Abs(clo2)) =>
      conv(env.next, clo1(Sem.Var(env)), clo2(Sem.Var(env)))

    case (Sem.App(operator1, operand1), Sem.App(operator2, operand2)) =>
      conv(env, operator1, operator2) && conv(env, operand1, operand2)

    case (Sem.Sum(variants1), Sem.Sum(variants2)) =>
      (variants1 zip variants2).forall(conv(env, _, _))

    case (Sem.Inj(index1, target1), Sem.Inj(index2, target2)) =>
      index1 == index2 && conv(env, target1, target2)

    case (Sem.Var(lvl1), Sem.Var(lvl2)) =>
      lvl1 == lvl2

    case _ =>
      false

  private type Typ = Sem

  private final case class Ctx(sems: Env, typs: Vector[Typ]) with
    def toLvl: Lvl = Lvl(sems.size)

  private object Ctx with
    def empty: Ctx = Ctx(Vector.empty, Vector.empty)

  extension (typ: Typ) private def +: (ctx: Ctx): Ctx =
    Ctx(Sem.Var(ctx.toLvl) +: ctx.sems, typ +: ctx.typs)

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

    case Exp.Abs(body) =>
      ??? // TODO: error message

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

    case Exp.Inj(index, target) =>
      ??? // TODO: error message

    case Exp.Var(idx) =>
      Some(ctx.typs(idx.toInt))

    case Exp.Ann(target, annotation) =>
      for
        _ <- inferTyp(ctx, annotation)
        annotation <- Some(reflect(ctx.sems, annotation))
        _ <- check(ctx, target, annotation)
      yield annotation

  private def check(ctx: Ctx, exp: Exp, typ: Typ): Option[Unit] = (exp, typ) match
    case (Exp.Abs(body), Sem.Fun(domain, codomain)) =>
      check(domain +: ctx, body, codomain(Sem.Var(ctx.toLvl)))

    case (Exp.Inj(index, target), Sem.Sum(variants)) =>
      for
        variant <- variants.lift(index)
        _ <- check(ctx, target, variant)
      yield ()

    case (exp, typ) =>
      for
        t <- infer(ctx, exp)
        if conv(ctx.toLvl, t, typ)
      yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- infer(Ctx.empty, exp) yield exp

package mcl.phase

import Levels.*
import mcl.ast.Core.Exp
import mcl.ast.Indices.*
import scala.language.postfixOps

object Type extends (Exp => Option[Exp]):
  private type Env = Vector[Sem]

  private final case class Clo(env: Env, body: Exp) with
    def apply(operand: Sem): Sem = (+body)(using operand +: env)

  private enum Sem with
    case Typ(level: Int)
    case Fun(domain: Sem, clo: Clo)
    case Abs(clo: Clo)
    case App(operator: Sem, operand: Sem)
    case Sum(variants: Seq[Sem])
    case Inj(index: Int, target: Sem)
    case Fix(body: Sem)
    case Var(lvl: Lvl)

  extension (exp: Exp) private def unary_+ (using env: Env): Sem = exp match
    case Exp.Typ(level) =>
      Sem.Typ(level)

    case Exp.Fun(domain, codomain) =>
      Sem.Fun(+domain, Clo(env, codomain))

    case Exp.Abs(body) =>
      Sem.Abs(Clo(env, body))

    case Exp.App(operator, operand) => (+operator, +operand) match
      case (Sem.Abs(clo), operand) => clo(operand)
      case (operator, operand) => Sem.App(operator, operand)

    case Exp.Sum(variants) =>
      Sem.Sum(variants.map(+_))

    case Exp.Inj(index, target) =>
      Sem.Inj(index, +target)

    case Exp.Fix(body) =>
      +body

    case Exp.Var(idx) =>
      env(idx.toInt)

    case Exp.Ann(target, _) =>
      +target

  extension (sem: Sem) private def unary_- (using env: Lvl): Exp = sem match
    case Sem.Typ(level) =>
      Exp.Typ(level)

    case Sem.Fun(domain, clo) =>
      Exp.Fun(-domain, (-clo(Sem.Var(env)))(using env+))

    case Sem.Abs(clo) =>
      Exp.Abs((-clo(Sem.Var(env)))(using env+))

    case Sem.App(operator, operand) =>
      Exp.App(-operator, -operand)

    case Sem.Sum(variants) =>
      Exp.Sum(variants.map(-_))

    case Sem.Inj(index, target) =>
      Exp.Inj(index, -target)

    case Sem.Fix(_) =>
      ???

    case Sem.Var(lvl) =>
      Exp.Var(lvl.toIdx(env))

  extension (sem1: Sem) private def === (sem2: Sem)(using env: Lvl): Boolean = (sem1, sem2) match
    case (Sem.Typ(level1), Sem.Typ(level2)) =>
      level1 == level2

    case (Sem.Fun(domain1, clo1), Sem.Fun(domain2, clo2)) =>
      domain1 === domain2 && (clo1(Sem.Var(env)) === (clo2(Sem.Var(env))))(using env+)

    case (Sem.Abs(clo1), Sem.Abs(clo2)) =>
      (clo1(Sem.Var(env)) === clo2(Sem.Var(env)))(using env+)

    case (Sem.App(operator1, operand1), Sem.App(operator2, operand2)) =>
      operator1 === operator2 && operand1 === operand2

    case (Sem.Sum(variants1), Sem.Sum(variants2)) =>
      (variants1 zip variants2).forall(_ === _)

    case (Sem.Inj(index1, target1), Sem.Inj(index2, target2)) =>
      index1 == index2 && target1 === target2

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

  extension (exp: Exp) private def *=> (using Ctx): Option[Int] =
    for Sem.Typ(level) <- exp ==> yield level

  extension (exp: Exp) private def ==> (using ctx: Ctx): Option[Typ] = exp match
    case Exp.Typ(level) =>
      Some(Sem.Typ(level + 1))

    case Exp.Fun(domain, codomain) =>
      for
        domainLevel <- (domain *=>)
        codomainLevel <- (codomain *=>)(using (+domain)(using ctx.sems) +: ctx)
      yield Sem.Typ(domainLevel max codomainLevel)

    case Exp.Abs(_) =>
      ???

    case Exp.App(operator, operand) =>
      for
        Sem.Fun(domain, clo) <- (operator ==>)
        _ <- operand <== domain
      yield clo((+operand)(using ctx.sems))

    case Exp.Sum(variants) =>
      val levels = for
        variant <- variants
        level <- (variant *=>)
      yield level
      for
        maxLevel <- levels.maxOption
      yield Sem.Typ(maxLevel)

    case Exp.Inj(_, _) =>
      ???

    case Exp.Fix(_) =>
      ???

    case Exp.Var(idx) =>
      Some(ctx.typs(idx.toInt))

    case Exp.Ann(target, annotation) =>
      for
        _ <- (annotation *=>)
        annotation <- Some((+annotation)(using ctx.sems))
        _ <- target <== annotation
      yield annotation

  extension (exp: Exp) private def <== (typ: Typ)(using ctx: Ctx): Option[Unit] = (exp, typ) match
    case (Exp.Abs(body), Sem.Fun(domain, codomain)) =>
      (body <== codomain(Sem.Var(ctx.toLvl)))(using domain +: ctx)

    case (Exp.Inj(index, target), Sem.Sum(variants)) =>
      for
        variant <- variants.lift(index)
        _ <- target <== variant
      yield ()

    case (Exp.Fix(body), typ) =>
      (body <== typ)(using typ +: ctx)

    case (exp, typ) =>
      for t <- (exp ==>) if (t === typ)(using ctx.toLvl) yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- (exp ==>)(using Ctx.empty) yield exp

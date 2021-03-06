package mcl.phase

object Type extends (Type.Exp => Option[Type.Exp]):
  import Indices._
  private object Indices with
    opaque type Idx = Int

    object Idx with
      def apply(idx: Int): Idx = idx

    extension (idx: Idx) def toInt: Int = idx

  enum Exp with
    case Typ(level: Int)
    case Fun(domain: Exp, codomain: Exp)
    case Abs(domain: Exp, body: Exp)
    case App(operator: Exp, operand: Exp)
    case Var(idx: Idx)

  import Levels._
  private object Levels with
    opaque type Lvl = Int

    object Lvl with
      def apply(lvl: Int): Lvl = lvl

    extension (lvl: Lvl)
      def next: Lvl = lvl + 1
      def toIdx(env: Lvl): Idx = Idx(lvl - env - 1)

  private type Ctx = Seq[Sem]

  private final case class Clo(env: Ctx, body: Exp) with
    def apply(operand: Sem): Sem = reflect(operand +: env, body)

  private enum Sem with
    case Typ(level: Int)
    case Fun(domain: Sem, clo: Clo)
    case Abs(domain: Sem, clo: Clo)
    case App(operator: Sem, operand: Sem)
    case Var(lvl: Lvl)

  private def reflect(env: Ctx, exp: Exp): Sem = exp match
    case Exp.Typ(level) =>
      Sem.Typ(level)

    case Exp.Fun(domain, codomain) =>
      Sem.Fun(reflect(env, domain), Clo(env, codomain))

    case Exp.Abs(domain, body) =>
      Sem.Abs(reflect(env, domain), Clo(env, body))

    case Exp.App(operator, operand) => (reflect(env, operator), reflect(env, operand)) match
      case (Sem.Abs(_, clo), operand) => clo(operand)
      case (operator, operand) => Sem.App(operator, operand)

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

    case (Sem.Var(lvl1), Sem.Var(lvl2)) =>
      lvl1 == lvl2

    case _ =>
      false

  private type Typ = Sem

  private def inferTyp(ctx: Ctx, exp: Exp): Option[Int] =
    for
      typ <- infer(ctx, exp)
      Sem.Typ(level) = typ
    yield level

  private def inferFun(ctx: Ctx, exp: Exp): Option[Typ] =
    for
      typ <- infer(ctx, exp)
      result @ Sem.Fun(_, _) = typ
    yield result

  private def infer(ctx: Ctx, exp: Exp): Option[Typ] = exp match
    case Exp.Typ(level) =>
      Some(Sem.Typ(level + 1))

    case Exp.Fun(domain, codomain) =>
      for
        domainLevel <- inferTyp(ctx, domain)
        codomainLevel <- inferTyp(reflect(Seq.empty, domain) +: ctx, codomain)
      yield Sem.Typ(domainLevel max codomainLevel)

    case Exp.Abs(domain, body) =>
      for
        _ <- inferTyp(ctx, domain)
        domain <- Some(reflect(Seq.empty, domain))
        _ <- infer(domain +: ctx, body)
      yield Sem.Fun(domain, Clo(Seq.empty, body))

    case Exp.App(operator, operand) =>
      for
        Sem.Fun(domain, abs) <- inferFun(ctx, operator)
        _ <- check(ctx, operand, domain)
      yield abs(reflect(Seq.empty, operand))

    case Exp.Var(idx) =>
      ctx.lift(idx.toInt)

  private def check(ctx: Ctx, exp: Exp, typ: Typ): Option[Unit] =
    for t <- infer(ctx, exp) if conv(Lvl(ctx.size), t, typ) yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- infer(Seq.empty, exp) yield exp

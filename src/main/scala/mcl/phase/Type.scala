package mcl.phase

import mcl.ast.Source.Term as S

// TODO: normalization
// TODO: substitution
object Type extends (S => Option[S]):
  type Ctx = Map[Int, S]

  private def normalize(term: S): S = ???

  private def substitute(term: S, subst: Map[Int, S]): S = ???

  private def inferConstrained[T <: S](term: S)(using ctx: Ctx): Option[T] =
    for
      typ <- infer(term)
      result = normalize(typ) if result.isInstanceOf[T]
    yield result.asInstanceOf[T]

  private def infer(term: S)(using ctx: Ctx): Option[S] = term match
    case S.Type(level) =>
      Some(S.Type(level + 1))

    case S.Fun(id, domain, codomain) =>
      for
        S.Type(domainLevel) <- inferConstrained[S.Type](domain)
        S.Type(codomainLevel) <- inferConstrained[S.Type](codomain)(using ctx + (id -> domain))
      yield S.Type(domainLevel max codomainLevel)

    case S.App(operator, operand) =>
      for
        S.Fun(id, domain, codomain) <- inferConstrained[S.Fun](operator)
        _ <- check(operand, domain)
      yield substitute(codomain, Map(id -> operand))

    case S.Var(id) =>
      ctx.get(id)

    case S.Anno(target, annotation) =>
      for _ <- check(target, annotation) yield annotation

    case _ =>
      None

  private def check(term: S, typ: S)(using ctx: Ctx): Option[Unit] = (term, typ) match
    case (S.Abs(id, body), S.Fun(_, domain, codomain)) =>
      for
        _ <- inferConstrained[S.Type](domain)
        _ <- check(body, codomain)(using ctx + (id -> domain))
      yield ()

    case (term, typ) =>
      for typ1 <- infer(term) if typ == typ1 yield ()

  def apply(source: S): Option[S] = infer(source)(using Map.empty)

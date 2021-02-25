package mcl.phase

import mcl.ast.Source.Term as S

// TODO: normalization-by-evaluation
object Type extends (S => Option[S]):
  type Ctx = Map[Int, S]

  private def substitute(term: S)(using subst: Map[Int, S]): S = term match
    case S.Fun(id, domain, codomain) =>
      S.Fun(id, substitute(domain), substitute(codomain))

    case S.Abs(id, domain, body) =>
      S.Abs(id, substitute(domain), substitute(body))

    case S.App(operator, operand) =>
      S.App(substitute(operator), substitute(operand))

    case S.Var(id) if subst contains id =>
      subst(id)

    case S.Ind(id, constructors, body) =>
      S.Ind(id, constructors, substitute(body))

    case term =>
      term

  private def normalize(term: S): S = term match
    case S.Fun(id, domain, codomain) =>
      S.Fun(id, normalize(domain), normalize(codomain))

    case S.Abs(id, domain, body) =>
      S.Abs(id, normalize(domain), normalize(body))

    case S.App(operator, operand) =>
      normalize(operator) match
      case S.Abs(id, domain, body) =>
        normalize(substitute(body)(using Map(id -> normalize(operand))))
      case operator =>
        S.App(operator, normalize(operand))

    case S.Ind(id, constructors, body) =>
      S.Ind(id, constructors, normalize(body))

    case term =>
      term

  private def inferType(term: S)(using ctx: Ctx): Option[S] =
    for
      typ <- infer(term)
      result @ S.Type(_) = normalize(typ)
    yield result

  private def inferFun(term: S)(using ctx: Ctx): Option[S] =
    for
      typ <- infer(term)
      result @ S.Fun(_, _, _) = normalize(typ)
    yield result

  private def infer(term: S)(using ctx: Ctx): Option[S] = term match
    case S.Type(level) =>
      Some(S.Type(level + 1))

    case S.Fun(id, domain, codomain) =>
      for
        S.Type(domainLevel) <- inferType(domain)
        S.Type(codomainLevel) <- inferType(codomain)(using ctx + (id -> domain))
      yield S.Type(domainLevel max codomainLevel)

    case S.Abs(id, domain, body) =>
      for
        _ <- inferType(domain)
        codomain <- infer(body)(using ctx + (id -> domain))
      yield S.Fun(id, domain, codomain)

    case S.App(operator, operand) =>
      for
        S.Fun(id, domain, codomain) <- inferFun(operator)
        if check(operand, domain)
      yield substitute(codomain)(using Map(id -> operand))

    case S.Var(id) =>
      ctx.get(id)

    case S.Ind(id, constructors, body) =>
      infer(body)(using ctx + (id -> S.Type(0)) ++ constructors.map(_ -> S.Var(id)))

  private def check(term: S, typ: S)(using ctx: Ctx): Boolean =
    infer(term).map(_ == typ).getOrElse(false)

  def apply(source: S): Option[S] = infer(source)(using Map.empty)

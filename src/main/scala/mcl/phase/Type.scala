package mcl.phase

import mcl.Sym
import mcl.ast.Source.Term as S

object Type extends (S => Option[S]):
  private enum Semantics with
    case Abs(fun: Semantics => Semantics)
    case Acc(head: S, tail: Seq[Semantics])

    def apply(operand: Semantics): Semantics = this match
      case Abs(fun) =>
        fun(operand)

      case Acc(id, tail) =>
        Acc(id, tail :+ operand)

  private def reflect(term: S)(using ctx: Map[Sym, Semantics]): Semantics = term match
    case S.Abs(id, _, body) =>
      Semantics.Abs(parameter => reflect(body)(using ctx + (id -> parameter)))

    case S.App(operator, operand) =>
      reflect(operator)(reflect(operand))

    case S.Var(id) if ctx contains id =>
      ctx(id)

    case term =>
      Semantics.Acc(term, Seq.empty)

  private def reify(semantics: Semantics): S = semantics match
    case Semantics.Abs(fun) =>
      val id = Sym.fresh()
      S.Abs(id, S.Type(-1), reify(fun(Semantics.Acc(S.Var(id), Seq.empty))))

    case Semantics.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => S.App(operator, reify(operand)))

  private def normalize(term: S): S = reify(reflect(term)(using Map.empty))

  private def substitute(term: S)(using subst: Map[Sym, S]): S = term match
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

  private def inferType(term: S)(using ctx: Map[Sym, S]): Option[S] =
    for
      typ <- infer(term)
      result @ S.Type(_) = normalize(typ)
    yield result

  private def inferFun(term: S)(using ctx: Map[Sym, S]): Option[S] =
    for
      typ <- infer(term)
      result @ S.Fun(_, _, _) = normalize(typ)
    yield result

  private def infer(term: S)(using ctx: Map[Sym, S]): Option[S] = term match
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

  private def check(term: S, typ: S)(using ctx: Map[Sym, S]): Boolean =
    infer(term).map(_ == typ).getOrElse(false)

  def apply(source: S): Option[S] =
    for _ <- infer(source)(using Map.empty) yield source

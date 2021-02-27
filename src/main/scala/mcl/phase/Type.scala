package mcl.phase

import mcl.Sym
import mcl.ast.Source.Term as S

object Type extends (S => Option[S]):
  private enum Semantics with
    case Abs(domain: Semantics, abs: Semantics => Semantics, reifier: (Sym, S, S) => S)
    case Acc(head: S, tail: Seq[Semantics] = Seq.empty)

    def apply(operand: Semantics): Semantics = this match
      case Abs(_, abs, _) =>
        abs(operand)

      case Acc(id, tail) =>
        Acc(id, tail :+ operand)

    def === (that: Semantics): Boolean = (this, that) match
      case (Abs(domain1, abs1, reifier1), Abs(domain2, abs2, reifier2)) =>
        val dummy = Acc(S.Var(Sym.fresh()))
        reifier1 == reifier2 && domain1 === domain2 && abs1(dummy) === abs2(dummy)

      case (Acc(head1, tail1), Acc(head2, tail2)) =>
        head1 == head2 && tail1.zip(tail2).forall(_ === _)

      case _ =>
        false

  private val reifierFun = S.Fun.apply
  private val reifierAbs = S.Abs.apply

  private def reflect(term: S)(using ctx: Map[Sym, Semantics] = Map.empty): Semantics = term match
    case S.Fun(id, domain, codomain) =>
      Semantics.Abs(reflect(domain), parameter => reflect(codomain)(using ctx + (id -> parameter)), reifierFun)

    case S.Abs(id, domain, body) =>
      Semantics.Abs(reflect(domain), parameter => reflect(body)(using ctx + (id -> parameter)), reifierAbs)

    case S.App(operator, operand) =>
      reflect(operator)(reflect(operand))

    case S.Var(id) if ctx contains id =>
      ctx(id)

    case term =>
      Semantics.Acc(term)

  private def reify(semantics: Semantics): S = semantics match
    case Semantics.Abs(domain, abs, reifier) =>
      val id = Sym.fresh()
      reifier(id, reify(domain), reify(abs(Semantics.Acc(S.Var(id)))))

    case Semantics.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => S.App(operator, reify(operand)))

  private def normalize(term: S): S = (reify compose reflect)(term)

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
    infer(term).map(reflect(_) === reflect(typ)).getOrElse(false)

  def apply(source: S): Option[S] =
    for _ <- infer(source)(using Map.empty) yield source

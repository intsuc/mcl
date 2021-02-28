package mcl.phase

import mcl.Sym
import mcl.ast.Source.Term as S

object Type extends (S => Option[S]):
  private enum Semantics with
    case Abs(domain: Semantics, abstraction: Semantics => Semantics, constructor: (Sym, S, S) => S)
    case Acc(head: S, tail: Seq[Semantics] = Seq.empty)

  extension (semantics1: Semantics) private def === (semantics2: Semantics): Boolean = (semantics1, semantics2) match
    case (Semantics.Abs(domain1, abstraction1, constructor1), Semantics.Abs(domain2, abstraction2, constructor2)) =>
      constructor1 == constructor2 && domain1 === domain2 && {
        val dummy = Semantics.Acc(S.Var(Sym.fresh()))
        abstraction1(dummy) === abstraction2(dummy)
      }

    case (Semantics.Acc(head1, tail1), Semantics.Acc(head2, tail2)) =>
      head1 == head2 && (tail1 zip tail2).forall(_ === _)

    case _ =>
      false

  extension (operator: S) private def apply(operand: S): Semantics = reflect(operator) match
    case Semantics.Abs(_, abstraction, _) =>
      abstraction(reflect(operand))

    case Semantics.Acc(head, tail) =>
      Semantics.Acc(head, tail :+ reflect(operand))

  private val constructorFun = S.Fun.apply
  private val constructorAbs = S.Abs.apply

  private def reflect(term: S)(using ctx: Map[Sym, Semantics] = Map.empty): Semantics = term match
    case S.Fun(id, domain, codomain) =>
      Semantics.Abs(reflect(domain), semantics => reflect(codomain)(using ctx + (id -> semantics)), constructorFun)

    case S.Abs(id, domain, body) =>
      Semantics.Abs(reflect(domain), semantics => reflect(body)(using ctx + (id -> semantics)), constructorAbs)

    case S.App(operator, operand) =>
      operator(operand)

    case S.Var(id) if ctx contains id =>
      ctx(id)

    case term =>
      Semantics.Acc(term)

  private def reify(semantics: Semantics): S = semantics match
    case Semantics.Abs(domain, abstraction, reifier) =>
      val id = Sym.fresh()
      reifier(id, reify(domain), reify(abstraction(Semantics.Acc(S.Var(id)))))

    case Semantics.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => S.App(operator, reify(operand)))

  private def normalize(term: S): S = (reify compose reflect)(term)

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
        fun @ S.Fun(_, domain, _) <- inferFun(operator)
        if check(operand, domain)
      yield reify(fun(operand))

    case S.Var(id) =>
      ctx.get(id)

    case S.Ind(id, constructors, body) =>
      infer(body)(using ctx + (id -> S.Type(0)) ++ constructors.map(_ -> S.Var(id)))

  private def check(term: S, typ: S)(using ctx: Map[Sym, S]): Boolean =
    infer(term).map(reflect(_) === reflect(typ)).getOrElse(false)

  def apply(source: S): Option[S] =
    for _ <- infer(source)(using Map.empty) yield source

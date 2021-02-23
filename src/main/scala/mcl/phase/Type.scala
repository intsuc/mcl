package mcl.phase

import mcl.ast.Source.Term as S
import mcl.ast.Typed.Term as T

// TODO: normalization
object Type extends (S => Option[T]):
  def apply(source: S): Option[T] = synth(source)(using Map.empty)

  private def synth(term: S)(using ctx: Map[Int, S]): Option[T] = term match
    case S.Prop =>
      Some(T.Prop(S.Type(1)))

    case S.Type(level) =>
      Some(T.Type(level, S.Type(level + 1)))

    case S.Fun(id, domain, codomain) =>
      for
        domain <- synth(domain)
        codomain <- synth(codomain)(using ctx + (id -> domain.typ))
        S.Type(level1) = domain.typ
        S.Type(level2) = codomain.typ
        level = level1 max level2
      yield T.Type(level, S.Type(level + 1))

    case S.App(operator, operand) =>
      for
        operator <- synth(operator)
        typ @ S.Fun(_, domain, codomain) = operator.typ
        operand <- check(operand, domain)
      yield T.App(operator, operand, typ)

    case S.Var(id) =>
      for typ <- ctx.get(id) yield T.Var(id, typ)

    case S.Anno(target, annotation) =>
      check(target, annotation)

    case _ =>
      None

  private def check(term: S, typ: S)(using ctx: Map[Int, S]): Option[T] = (term, typ) match
    case (S.Abs(id1, body), typ @ S.Fun(id2, domain, codomain)) =>
      for body <- check(body, codomain)(using ctx + (id1 -> domain)) yield T.Abs(id1, body, typ)

    case (term, typ) =>
      for typ1 <- synth(term) if typ == typ1 yield typ1

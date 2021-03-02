package mcl.phase

import mcl.Sym
import mcl.ast.Source as S

object Type extends (S.Exp => Option[S.Exp]):
  private enum Sem with
    case Fun(domain: Sem, fum: Sem => Sem)
    case Abs(domain: Sem, abs: Sem => Sem)
    case Acc(head: S.Exp, tail: Seq[Sem] = Seq.empty)

  extension (operator: S.Exp) private def apply(operand: S.Exp): Sem = reflect(operator) match
    case Sem.Fun(_, fun) =>
      fun(reflect(operand))

    case Sem.Abs(_, abs) =>
      abs(reflect(operand))

    case Sem.Acc(head, tail) =>
      Sem.Acc(head, tail :+ reflect(operand))

  private def reflect(exp: S.Exp)(using ctx: Map[Sym, Sem] = Map.empty): Sem = exp match
    case S.Exp.Fun(id, domain, codomain) =>
      Sem.Fun(reflect(domain), sem => reflect(codomain)(using ctx + (id -> sem)))

    case S.Exp.Abs(id, domain, body) =>
      Sem.Abs(reflect(domain), sem => reflect(body)(using ctx + (id -> sem)))

    case S.Exp.App(operator, operand) =>
      operator(operand)

    case S.Exp.Var(id) if ctx contains id =>
      ctx(id)

    case exp =>
      Sem.Acc(exp)

  private def reify(sem: Sem): S.Exp = sem match
    case Sem.Fun(domain, abstraction) =>
      val id = Sym.fresh()
      S.Exp.Fun(id, reify(domain), reify(abstraction(Sem.Acc(S.Exp.Var(id)))))

    case Sem.Abs(domain, abstraction) =>
      val id = Sym.fresh()
      S.Exp.Abs(id, reify(domain), reify(abstraction(Sem.Acc(S.Exp.Var(id)))))

    case Sem.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => S.Exp.App(operator, reify(operand)))

  private def normalize(exp: S.Exp): S.Exp = (reify compose reflect)(exp)

  extension (exp1: S.Exp) private def === (exp2: S.Exp): Boolean =
    extension (sem1: Sem) def === (sem2: Sem): Boolean = (sem1, sem2) match
      case (Sem.Fun(domain1, fun1), Sem.Fun(domain2, fun2)) =>
        domain1 === domain2 && {
          val dummy = Sem.Acc(S.Exp.Var(Sym.fresh()))
          fun1(dummy) === fun2(dummy)
        }

      case (Sem.Abs(domain1, abs1), Sem.Abs(domain2, abs2)) =>
        domain1 === domain2 && {
          val dummy = Sem.Acc(S.Exp.Var(Sym.fresh()))
          abs1(dummy) === abs2(dummy)
        }

      case (Sem.Acc(head1, tail1), Sem.Acc(head2, tail2)) =>
        head1 == head2 && (tail1 zip tail2).forall(_ === _)

      case _ =>
        false

    reflect(exp1) === reflect(exp2)

  private def inferType(exp: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[S.Exp] =
    for
      typ <- infer(exp)
      result @ S.Exp.Type(_) = normalize(typ)
    yield result

  private def inferFun(exp: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[S.Exp] =
    for
      typ <- infer(exp)
      result @ S.Exp.Fun(_, _, _) = normalize(typ)
    yield result

  private def infer(exp: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[S.Exp] = exp match
    case S.Exp.Type(level) =>
      Some(S.Exp.Type(level + 1))

    case S.Exp.Fun(id, domain, codomain) =>
      for
        S.Exp.Type(domainLevel) <- inferType(domain)
        S.Exp.Type(codomainLevel) <- inferType(codomain)(using ctx + (id -> domain))
      yield S.Exp.Type(domainLevel max codomainLevel)

    case S.Exp.Abs(id, domain, body) =>
      for
        _ <- inferType(domain)
        codomain <- infer(body)(using ctx + (id -> domain))
      yield S.Exp.Fun(id, domain, codomain)

    case S.Exp.App(operator, operand) =>
      for
        fun @ S.Exp.Fun(_, domain, _) <- inferFun(operator)
        _ <- check(operand, domain)
      yield reify(fun(operand))

    case S.Exp.Var(id) =>
      ctx.get(id)

    case S.Exp.Ind(id, arity, constructors, body) =>
      def result(typ: S.Exp): S.Exp = typ match
        case S.Exp.Fun(_, _, codomain) => result(codomain)
        case typ => typ

      def level(typ: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[Int] = typ match
        case S.Exp.Type(level) => Some(level)
        case S.Exp.Fun(_, domain, codomain) =>
          for
            domain <- level(domain)
            codomain <- level(codomain)
          yield domain max codomain
        case S.Exp.Abs(_, _, body) => level(body)
        case S.Exp.App(operator, operand) => ???
        case S.Exp.Var(id) => ctx.get(id).flatMap(level)
        case S.Exp.Ind(_, _, _, body) => level(body)

      def parameters(typ: S.Exp): Seq[S.Exp] = typ match
        case S.Exp.Fun(_, domain, codomain) => domain +: parameters(codomain)
        case typ => Seq(typ)

      def positive(id: Sym, typ: S.Exp, pos: Boolean): Boolean = typ match
        case S.Exp.Fun(_, domain, codomain) => positive(id, domain, !pos) && positive(id, codomain, pos)
        case S.Exp.Var(id1) if id == id1 => pos
        case _ => true

      for
        arityLevel <- level(arity)
        if constructors.forall((_, typ) => result(typ) === S.Exp.Var(id) && {
          val normalized = normalize(typ)
          for
            constructorLevel <- level(normalized)(using ctx + (id -> S.Exp.Type(arityLevel - 1)))
            if constructorLevel < arityLevel && parameters(normalized).forall(positive(id, _, true))
          yield ()
        }.isDefined)
        body <- infer(body)(using ctx + (id -> arity) ++ constructors)
      yield body

  private def check(exp: S.Exp, typ: S.Exp)(using ctx: Map[Sym, S.Exp]): Option[Unit] =
    for typ1 <- infer(exp) if typ1 === typ yield ()

  def apply(exp: S.Exp): Option[S.Exp] =
    for _ <- infer(exp)(using Map.empty) yield exp

package mcl.phase

import mcl.Sym
import mcl.ast.Source.Exp

object Type extends (Exp => Option[Exp]):
  private enum Sem with
    case Fun(domain: Sem, fum: Sem => Sem)
    case Abs(domain: Sem, abs: Sem => Sem)
    case Acc(head: Exp, tail: Seq[Sem] = Seq.empty)

  extension (operator: Exp) private def apply(operand: Exp): Sem = reflect(operator) match
    case Sem.Fun(_, fun) =>
      fun(reflect(operand))

    case Sem.Abs(_, abs) =>
      abs(reflect(operand))

    case Sem.Acc(head, tail) =>
      Sem.Acc(head, tail :+ reflect(operand))

  private def reflect(exp: Exp)(using ctx: Map[Sym, Sem] = Map.empty): Sem = exp match
    case Exp.Fun(id, domain, codomain) =>
      Sem.Fun(reflect(domain), sem => reflect(codomain)(using ctx + (id -> sem)))

    case Exp.Abs(id, domain, body) =>
      Sem.Abs(reflect(domain), sem => reflect(body)(using ctx + (id -> sem)))

    case Exp.App(operator, operand) =>
      operator(operand)

    case Exp.Var(id) if ctx contains id =>
      ctx(id)

    case exp =>
      Sem.Acc(exp)

  private def reify(sem: Sem): Exp = sem match
    case Sem.Fun(domain, abstraction) =>
      val id = Sym.fresh()
      Exp.Fun(id, reify(domain), reify(abstraction(Sem.Acc(Exp.Var(id)))))

    case Sem.Abs(domain, abstraction) =>
      val id = Sym.fresh()
      Exp.Abs(id, reify(domain), reify(abstraction(Sem.Acc(Exp.Var(id)))))

    case Sem.Acc(head, tail) =>
      tail.foldLeft(head)((operator, operand) => Exp.App(operator, reify(operand)))

  private def normalize(exp: Exp): Exp = (reify compose reflect)(exp)

  extension (exp1: Exp) private def === (exp2: Exp): Boolean =
    extension (sem1: Sem) def === (sem2: Sem): Boolean = (sem1, sem2) match
      case (Sem.Fun(domain1, fun1), Sem.Fun(domain2, fun2)) =>
        domain1 === domain2 && {
          val dummy = Sem.Acc(Exp.Var(Sym.fresh()))
          fun1(dummy) === fun2(dummy)
        }

      case (Sem.Abs(domain1, abs1), Sem.Abs(domain2, abs2)) =>
        domain1 === domain2 && {
          val dummy = Sem.Acc(Exp.Var(Sym.fresh()))
          abs1(dummy) === abs2(dummy)
        }

      case (Sem.Acc(head1, tail1), Sem.Acc(head2, tail2)) =>
        head1 == head2 && (tail1 zip tail2).forall(_ === _)

      case _ =>
        false

    reflect(exp1) === reflect(exp2)

  private type Typ = Exp

  private def inferType(exp: Exp)(using ctx: Map[Sym, Typ]): Option[Exp] =
    for
      typ <- infer(exp)
      result @ Exp.Type(_) = normalize(typ)
    yield result

  private def inferFun(exp: Exp)(using ctx: Map[Sym, Typ]): Option[Exp] =
    for
      typ <- infer(exp)
      result @ Exp.Fun(_, _, _) = normalize(typ)
    yield result

  private def infer(exp: Exp)(using ctx: Map[Sym, Typ]): Option[Exp] = exp match
    case Exp.Type(level) =>
      Some(Exp.Type(level + 1))

    case Exp.Fun(id, domain, codomain) =>
      for
        Exp.Type(domainLevel) <- inferType(domain)
        Exp.Type(codomainLevel) <- inferType(codomain)(using ctx + (id -> domain))
      yield Exp.Type(domainLevel max codomainLevel)

    case Exp.Abs(id, domain, body) =>
      for
        _ <- inferType(domain)
        codomain <- infer(body)(using ctx + (id -> domain))
      yield Exp.Fun(id, domain, codomain)

    case Exp.App(operator, operand) =>
      for
        fun @ Exp.Fun(_, domain, _) <- inferFun(operator)
        _ <- check(operand, domain)
      yield reify(fun(operand))

    case Exp.Var(id) =>
      ctx.get(id)

    case Exp.Ind(id, arity @ Exp.Type(_) /* normalize? */, constructors, body) =>
      def result(typ: Exp): Exp = typ match
        case Exp.Fun(_, _, codomain) => result(codomain)
        case typ => typ

      def level(typ: Exp)(using ctx: Map[Sym, Exp]): Option[Int] = typ match
        case Exp.Type(level) => Some(level)
        case Exp.Fun(_, domain, codomain) =>
          for
            domain <- level(domain)
            codomain <- level(codomain)
          yield domain max codomain
        case Exp.Abs(_, _, body) => level(body)
        case Exp.App(operator, operand) => ???
        case Exp.Var(id) => ctx.get(id).flatMap(level)
        case Exp.Ind(_, _, _, body) => level(body)

      def parameters(typ: Exp): Seq[Exp] = typ match
        case Exp.Fun(_, domain, codomain) => domain +: parameters(codomain)
        case typ => Seq(typ)

      def positive(id: Sym, typ: Exp, pos: Boolean): Boolean = typ match
        case Exp.Fun(_, domain, codomain) => positive(id, domain, !pos) && positive(id, codomain, pos)
        case Exp.Var(id1) if id == id1 => pos
        case _ => true

      for
        arityLevel <- level(arity)
        name = Exp.Var(id)
        if constructors forall { (_, typ) =>
          val normalized = normalize(typ)
          result(normalized) === name &&
          (for
            constructorLevel <- level(normalized)(using ctx + (id -> Exp.Type(arityLevel - 1)))
            if constructorLevel < arityLevel && parameters(normalized).forall(positive(id, _, true))
          yield ()).isDefined
        }
        body <- infer(body)(using ctx + (id -> arity) ++ constructors)
      yield body

  private def check(exp: Exp, typ: Exp)(using Map[Sym, Typ]): Option[Unit] =
    for typ1 <- infer(exp) if typ1 === typ yield ()

  def apply(exp: Exp): Option[Exp] =
    for _ <- infer(exp)(using Map.empty) yield exp

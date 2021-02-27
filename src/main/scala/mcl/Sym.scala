package mcl

final case class Sym private (id: Int)

object Sym with
  private var id = 0

  def fresh(): Sym =
    id += 1
    Sym(id)

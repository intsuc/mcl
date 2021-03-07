package mcl.ast

object Indices with
  opaque type Idx = Int

  object Idx with
    def apply(idx: Int): Idx = idx

  extension (idx: Idx) def toInt: Int = idx

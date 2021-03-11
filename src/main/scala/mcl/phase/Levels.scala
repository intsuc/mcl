package mcl.phase

import mcl.ast.Indices.Idx

object Levels with
  opaque type Lvl = Int

  object Lvl with
    def apply(lvl: Int): Lvl = lvl

  extension (lvl: Lvl)
    def + : Lvl = lvl + 1

    def toIdx(env: Lvl): Idx = Idx(lvl - env - 1)

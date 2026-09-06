import InductiveModels.Main

/-- `lean-inductive-models [OPTIONS] IN.ndjson`; see [`InductiveModels.main`]. -/
def main (args : List String) : IO UInt32 :=
  InductiveModels.main args

import Lake
open Lake DSL

require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @
  "45061fa1a5b4bad876f17c03d3a5544d818622e6" / "backends/lean"
require papers4 from "../../../lean"

package «capsulecheck» {}

@[default_target] lean_lib «Capsule» where
  roots := #[`Capsule, `Authvar, `Secureboot, `AbstractAV, `AbstractSB,
             `Bridge, `BridgeAV, `BridgeSB]

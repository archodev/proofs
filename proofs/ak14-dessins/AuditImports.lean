import AK14
import Lean.Util.CollectAxioms

open Lean in
run_cmd
  let env ← getEnv
  let mut count := 0
  let mut modules := 0
  let permitted := #[`propext, `Classical.choice, `Quot.sound]
  for i in [:env.header.modules.size] do
    let mod := env.header.modules[i]!.module
    if Name.isPrefixOf `AK14 mod || Name.isPrefixOf `KirovDolbeault mod then
      modules := modules + 1
      for n in env.header.moduleData[i]!.constNames do
        count := count + 1
        for a in (← collectAxioms n) do
          unless permitted.contains a do
            throwError m!"Unexpected axiom {a} while inspecting {n} from {mod}"
  unless modules == 390 && count > 0 do
    throwError m!"Expected 390 imported AK14 and Kirov modules; found {modules} and {count} declarations"
  logInfo m!"Checked {count} declarations in {modules} imported AK14 and Kirov modules. All axioms are standard."

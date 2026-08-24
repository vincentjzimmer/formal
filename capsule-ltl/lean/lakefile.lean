import Lake
open Lake DSL

package papers4

lean_lib Papers4 where
  roots := #[`ltl_capsule, `AuthMonotone, `refine_capsule,
             `AbstractAdvance, `CapsuleInstance, `SecureBootInstance,
             `AuthVarInstance, `Composition]

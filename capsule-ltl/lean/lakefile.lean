import Lake
open Lake DSL

package «capsule-ltl» where
  -- Package configuration options

@[default_target]
lean_lib «UefiCapsuleLTL» where
  roots := #[`ltl_capsule, `refine_capsule, `AuthMonotone,
             `AuthVarInstance, `SecureBootInstance,
             `CapsuleInstance, `AbstractAdvance, `Composition]

set_option autoImplicit true
set_option relaxedAutoImplicit true

#print ReaderT
#print read -- * can be used unqualified
#print MonadReader

-- Let's explore how Lean finds instances automatically
#print ReaderT.instMonad

-- Check what instances are available in the current scope
#check @ReaderT.instMonad

-- Show the instance that Lean automatically finds
variable {ρ m} [Monad m] in
#synth Monad (ReaderT ρ m)

-- Show how instance search works for MonadReader
variable {ρ m} [Monad m] in
#synth (MonadReader ρ) (ReaderT ρ m)

-- Let's see what the actual instance looks like
variable {ρ m} [Monad m] in
#check (inferInstance : Monad (ReaderT ρ m))

-- Let's explore the namespace to see what instances exist
namespace ReaderT
#print instMonad
-- The MonadReader instance is likely defined elsewhere
end ReaderT

#print MonadLift
#print MonadLiftT
#print instMonadLiftT
#print instMonadLiftTOfMonadLift
#print ReaderT.instMonadLift
#print MonadWithReader

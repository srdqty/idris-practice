-- Local Variables:
-- idris-load-packages: ("prelude" "base" "contrib")
-- End:

-- Based on the following, updated for Idris 1.3.1
-- https://www.youtube.com/watch?v=P82dqVrS8ik
-- https://gist.github.com/puffnfresh/11360808

import Interfaces.Verified

data Option a = Some a | None

Semigroup a => Semigroup (Option a) where
  (Some a) <+> (Some b) = Some (a <+> b)
  None <+> a = a
  a <+> b = a

Semigroup a => Monoid (Option a) where
  neutral = None

VerifiedSemigroup a => VerifiedSemigroup (Option a) where
  semigroupOpIsAssociative (Some x) (Some y) (Some z) =
    cong (semigroupOpIsAssociative x y z)
  semigroupOpIsAssociative (Some x) (Some y) None = Refl
  semigroupOpIsAssociative (Some x) None z = Refl
  semigroupOpIsAssociative None y z = Refl

VerifiedSemigroup a => VerifiedMonoid (Option a) where
  monoidNeutralIsNeutralL (Some _) = Refl
  monoidNeutralIsNeutralL None = Refl
  monoidNeutralIsNeutralR (Some _) = Refl
  monoidNeutralIsNeutralR None = Refl

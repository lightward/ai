import Foam

namespace Foam.Exhibits

structure Exhibit where
  Claim : Prop
  receipt : Claim
  keyword : String
  famous : String
  provenance : String
  love : String
  note : String

end Foam.Exhibits

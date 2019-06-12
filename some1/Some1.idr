-- https://reasonablypolymorphic.com/some1-like-you/#/title

data Value
  = VObject (List (String, Value))
  | VArray (List Value)
  | VString String
  | VNumber Double
  | VBool Bool
  | VNull

interface FromJSON a where
  constructor MkFromJSON
  fromJSON : Value -> Maybe a

interface ToJSON a where
  constructor MkToJSON
  toJSON : a -> Value

data Meal = MkMeal
data Song = MkSong
data Duration = MkDuration

data PayloadWakeUp = MkPayloadWakeUp

implementation ToJSON PayloadWakeUp where
  toJSON _ = VNull

implementation FromJSON PayloadWakeUp where
  fromJSON _ = Nothing

data PayloadEat = MkPayloadEat Meal

implementation ToJSON PayloadEat where
  toJSON _ = VNull

implementation FromJSON PayloadEat where
  fromJSON _ = Nothing

data PayloadRockOut = MkPayloadRockOut Song Duration

implementation ToJSON PayloadRockOut where
  toJSON _ = VNull

implementation FromJSON PayloadRockOut where
  fromJSON _ = Nothing

data EventType = WakeUp | Eat | RockOut

implementation ToJSON EventType where
  toJSON WakeUp = VString "WakeUp"
  toJSON Eat = VString "Eat"
  toJSON RockOut = VString "RockOut"

implementation FromJSON EventType where
  fromJSON (VString "WakeUp") = Just WakeUp
  fromJSON (VString "Eat") = Just Eat
  fromJSON (VString "RockOut") = Just RockOut
  fromJSON _ = Nothing

Payload : EventType -> Type
Payload WakeUp = PayloadWakeUp
Payload Eat = PayloadEat
Payload RockOut = PayloadRockOut

plToJSON : (et : EventType) -> ToJSON (Payload et)
plToJSON WakeUp = MkToJSON toJSON
plToJSON Eat = MkToJSON toJSON
plToJSON RockOut = MkToJSON toJSON

plFromJSON : (et : EventType) -> FromJSON (Payload et)
plFromJSON WakeUp = MkFromJSON fromJSON
plFromJSON Eat = MkFromJSON fromJSON
plFromJSON RockOut = MkFromJSON fromJSON


data Event : Type where
  MkEvent : (et : EventType) -> Payload et -> Event

implementation ToJSON Event where
  toJSON (MkEvent et payload) =
    VObject [("type", toJSON et), ("payload", toJSON @{plToJSON et} payload)]

implementation FromJSON Event where
  fromJSON (VObject [("type", vet), ("payload", vpayload)]) =
    case the (Maybe EventType) (fromJSON vet) of
      Nothing => Nothing
      Just et => case fromJSON @{plFromJSON et} vpayload of
        Nothing => Nothing
        Just payload => Just (MkEvent et payload)

  fromJSON _ = Nothing

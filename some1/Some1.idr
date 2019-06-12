-- https://reasonablypolymorphic.com/some1-like-you/#/title

data Value
  = VObject (List (String, Value))
  | VArray (List Value)
  | VString String
  | VNumber Double
  | VBool Bool
  | VNull

interface FromJSON a where
  fromJSON : Value -> Maybe a

data FromJSONDict : Type -> Type where
  MkFromJSONDict : FromJSON a => FromJSONDict a

withFromJSONDict : FromJSONDict a -> (FromJSON a => r) -> r
withFromJSONDict MkFromJSONDict r = r

interface ToJSON a where
  toJSON : a -> Value

data ToJSONDict : Type -> Type where
  MkToJSONDict : ToJSON a => ToJSONDict a

withToJSONDict : ToJSONDict a -> (ToJSON a => r) -> r
withToJSONDict MkToJSONDict r = r

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

namespace Payload
  Payload : EventType -> Type
  Payload WakeUp = PayloadWakeUp
  Payload Eat = PayloadEat
  Payload RockOut = PayloadRockOut

  dictFromJSON : ( FromJSON (Payload WakeUp)
                 , FromJSON (Payload Eat)
                 , FromJSON (Payload RockOut)
                 )
               => (et : EventType)
               -> FromJSONDict (Payload et)
  dictFromJSON WakeUp = MkFromJSONDict
  dictFromJSON Eat = MkFromJSONDict
  dictFromJSON RockOut = MkFromJSONDict

  dictToJSON : ( ToJSON (Payload WakeUp)
               , ToJSON (Payload Eat)
               , ToJSON (Payload RockOut)
               )
             => (et : EventType)
             -> ToJSONDict (Payload et)
  dictToJSON WakeUp = MkToJSONDict
  dictToJSON Eat = MkToJSONDict
  dictToJSON RockOut = MkToJSONDict


data Event : Type where
  MkEvent : (et : EventType) -> Payload et -> Event

implementation ToJSON Event where
  toJSON (MkEvent et payload) =
    VObject [("type", toJSON et), ("payload", toJSON' et payload)]
  where
    toJSON' : (et : EventType) -> Payload et -> Value
    toJSON' et payload = withToJSONDict (dictToJSON et) (toJSON payload)

implementation FromJSON Event where
  fromJSON (VObject [("type", vet), ("payload", vpayload)]) =
    case the (Maybe EventType) (fromJSON vet) of
      Nothing => Nothing
      Just et => case fromJSON' et vpayload of
        Nothing => Nothing
        Just payload => Just (MkEvent et payload)
  where
    fromJSON' : (et : EventType) -> Value -> (Maybe (Payload et))
    fromJSON' et v = withFromJSONDict (dictFromJSON et) (fromJSON v)

  fromJSON _ = Nothing

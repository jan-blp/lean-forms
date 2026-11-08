module

public import Forms.Runtime.ModelForm
public import Forms.Runtime.InputProtocol

@[expose] public section
namespace Forms.Runtime.ModelProtocol

def eventFromWire : Wire.FormEvent → Except String ModelForm.Event
  | .draft key value => .ok (.draft ⟨key⟩ value)
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .submit => .ok .submit
  | .reset => .ok .reset
  | .complete status body => .ok (.complete (if 200 ≤ status && status < 300 then none
      else some (FeedbackProtocol.serverError status body)))
  | .failed message => .ok (.failed message)

def commandFromWire : Wire.FormRequest → Except String ModelForm.Command
  | .event message => ModelForm.Command.event <$> eventFromWire message
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .reset => .ok .reset
  | .validate => .ok .validate
  | .inspect => .ok .inspect
  | .serverError status body => .ok (.serverError (FeedbackProtocol.serverError status body))

end Forms.Runtime.ModelProtocol

module type DIGITAL_LIST = Signature.DIGITAL_LIST

module Dep = struct
  include Dep
end

module Non_dep = struct
  include Non_dep
end

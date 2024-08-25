Run tests with assertion failures in concolic:
  $ wasp concolic test1.wast
  Reached Assertion Failure!
  Model:
  [{"name" : "x", "value" : "(i32 0)", "type" : "i32"},{"name" : "y", "value" : "(i32 -2147483648)", "type" : "i32"},{"name" : "z", "value" : "(i32 1)", "type" : "i32"}]
  Found Problem!

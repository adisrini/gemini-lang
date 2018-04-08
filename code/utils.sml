structure Utils = 
struct

  fun vectorZipEq(v1, v2) = Vector.fromList(ListPair.zipEq(Vector.toList(v1), Vector.toList(v2)))

end
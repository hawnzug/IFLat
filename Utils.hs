module Utils where

hInitial   :: Heap a
hAlloc     :: Heap a -> a -> (Heap a, Addr)
hUpdate    :: Heap a -> Addr -> a -> Heap a
hFree      :: Heap a -> Addr -> Heap a
hLookup    :: Heap a -> Addr -> a
hAddresses :: Heap a -> [Addr]
hSize      :: Heap a -> Int
hNull :: Addr
hIsnull :: Addr -> Bool
showaddr :: Addr -> String

type Heap a = (Int, [Int], [(Int, a)])
type Addr = Int

hInitial = (0, [1..], [])
hAlloc (_, [], _) _ = error "cannot allocate space"
hAlloc (size, next:free, cts) n = ((size+1, free, (next,n):cts), next)
hUpdate (size, free, cts) a n = (size, free, (a,n):remove cts a)
hFree (size, free, cts) a = (size-1, a:free, remove cts a)
hLookup (_, _, cts) a = aLookup cts a (error ("cannot find node " ++ showaddr a ++ " in heap"))
hAddresses (_, _, cts) = [addr | (addr, _) <- cts]
hSize (size, _, _) = size
hNull = 0
hIsnull = (== 0)
showaddr a = "#" ++ show a

remove :: [(Int,a)] -> Int -> [(Int,a)]
remove [] a = error ("Attemp to update or free nonexistent address #" ++ show a)
remove ((a',n):cts) a | a == a' = cts
                      | a /= a' = (a',n):remove cts a
                      | otherwise = error "cannot reach"

type ASSOC a b = [(a,b)]

aLookup :: (Eq a) => [(a,b)] -> a -> b -> b
aLookup [] _ def = def
aLookup ((k,v):bs) k' def | k == k' = v
                          | k /= k' = aLookup bs k' def
                          | otherwise = error "cannot reach"

aDomain :: ASSOC a b -> [a]
aDomain alist = [key | (key, _) <- alist]

aRange :: ASSOC a b -> [b]
aRange alist = [val | (_, val) <- alist]

aEmpty :: ASSOC a b
aEmpty = []

mapAccuml :: (a -> b -> (a,c)) -> a -> [b] -> (a, [c])
mapAccuml _ acc [] = (acc, [])
mapAccuml f acc (x:xs) = (acc2, x':xs')
    where (acc1, x') = f acc x
          (acc2, xs') = mapAccuml f acc1 xs

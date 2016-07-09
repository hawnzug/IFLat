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

type Heap a = (Int, [Int], [(Int, a)], HeapStats)
type HeapStats = (Int, Int, Int)
type Addr = Int

getHeapStats :: Heap a -> HeapStats
getHeapStats (_,_,_,s) = s

incHeapAlloc :: HeapStats -> HeapStats
incHeapAlloc (alloc, update, free) = (alloc+1, update, free)
getHeapAlloc :: HeapStats -> Int
getHeapAlloc (alloc, _, _) = alloc

incHeapUpdate :: HeapStats -> HeapStats
incHeapUpdate (alloc, update, free) = (alloc, update+1, free)
getHeapUpdate :: HeapStats -> Int
getHeapUpdate (_, update, _) = update

incHeapFree :: HeapStats -> HeapStats
incHeapFree (alloc, update, free) = (alloc, update, free+1)
getHeapFree :: HeapStats -> Int
getHeapFree (_, _, free) = free

hInitial = (0, [1..], [], (0,0,0))
hAlloc (_, [], _, _) _ = error "cannot allocate space"
hAlloc (size, next:free, cts, stats) n = ((size+1, free, (next,n):cts, incHeapAlloc stats), next)
hUpdate (size, free, cts, stats) a n = (size, free, (a,n):remove cts a, incHeapUpdate stats)
hFree (size, free, cts, stats) a = (size-1, a:free, remove cts a, incHeapFree stats)
hLookup (_, _, cts, _) a = aLookup cts a (error ("cannot find node " ++ showaddr a ++ " in heap"))
hAddresses (_, _, cts, _) = [addr | (addr, _) <- cts]
hSize (size, _, _, _) = size
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

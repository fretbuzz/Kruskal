;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-advanced-reader.ss" "lang")((modname |mst -refined|) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #t #t none #f ())))
#|
Author: Joe Severini
Written in ASL (advanced student language) in Racket.

Note: Importing other files is tricky in ASL, so I have copied and pasted the contents of my UnionFind
and binary heap data structure implementations into the top of this file, which, while sloppy, is functional.
To see the new parts of this file, scroll below the unionfind and heap code to part 2.

In part 1, I copy and paste my code for unionfinds and binary heaps from the relevant files (also posted on github, with more
complete documentation and a robust testing apparatus).

In part 2, I implement a graph API, which consists of the following functions:
make-graph   : N -> WUGRAPH                        Creates a new undirected, wieghted graph with n disjoint vertices (i.e. no edges)
graph-size   : WUGRAPH -> N                        Returns number of vertices in graph (will remain constant throughout the graph's life)
get-edge     : WUGRAPH N N -> MaybeWeight          Gives the weight of the edge from N1 to N2
set-edge!    : WUGRAPH N N MaybeWeight -> Void     sets the weight of the edge from N1 to N2 to be N3
get-adjacent : WUGRAPH N -> [List-of-Vertex]       Returns a list of all the vertices adjacent to vertex N (Note: N must correspond to a vertex)
notInf       : N -> Bool                           If not infinity, returns true. Else returns false.

In part 3, I implemment Kruskal's algorithm using the graph API, UnionFind, and binary heap data structures.
kruskal-mst  : WUGraph -> WUGraph                  Returns a minimum spanning tree of the input graph using Kruskal's algorithm

Has complexity O(E log V), where  E is the number of edges in the graph and V is the number of vertices

NOTE: While this was assigned as a homework assignemnt for EECS214 at Northwestern University in the Fall of 2015, ALL code (including comments, function 
descriptions, the testing apparatus, and the tests as well as the actual code) are the sole work of the author.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PART 1A: UNIONFIND IMPLEMENTATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Union-find functions (i.e. public functions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-struct UnionFind [size data]) 
(define-struct UnionEntry [weight parent])

; uf:create: N -> UF
; creates a union-find structure of size 'size'. All sets are initialized with the parent being
; equal to itself. (i.e. all sets are initially disjoint). Numbered 0 to N-1.
(define (uf:create size)
  (make-UnionFind size (build-vector size makeUnionEntry)) )
(define (makeUnionEntry n)
  (make-UnionEntry 1 n))

; uf:size: UF -> N
; Returns the number of objects in the UF. (NOT the number of sets)
(define (size uf)
  (UnionFind-size uf))

(check-expect (size (uf:create 10)) 10)
(check-expect (size (uf:create 100)) 100)

; uf:same-set?: UF N N -> Bool
; Finds the base of each set and checks if they are equal (i.e. are in the same set)
(define (uf:same-set? uf obj1 obj2)
 (= (uf:find uf obj1) (uf:find uf obj2)) )    

; uf:find: UF N -> N
; Finds finds the base of the set of object 'obj' by recursively going to the parent. If the 
; parent is equal to the obj, then it is the base of the set. Also implements path compression-
; sets the parent of each examined node to the base of the set.
(define (uf:find uf obj)
  (cond
    [(= (uf:get-parent uf obj) obj) obj]        ;; at the root, can return
    [(not (=  (uf:get-parent uf obj) obj))
     (begin
       (set-UnionEntry-parent! (uf:get-entry uf obj) (uf:find uf (uf:get-parent uf obj)) ) ;; path compression
       (uf:get-parent uf obj))]
))

; uf:union!: UF N N -> Void
; Merges the set of 'obj1' with the set of 'obj2'. Does this by finding the base of each set. If the bases
; are the same, do nothing. If they are different, the 'heavier' set becomes the parent of the 'less heavy'
; set.
(define (uf:union! uf obj1 obj2)
  (local
    [(define root1 (uf:find uf obj1))
     (define root2 (uf:find uf obj2))
     (define weight1 (uf:get-weight uf root1))
     (define weight2 (uf:get-weight uf root2))]
  (cond
    [(uf:same-set? uf root1 root2) void]
    [else
     (cond      ;; heavier wieght on top
       [(or (< weight1 weight2) (= weight1 weight2)) 
            (uf:reparent! uf root1 root2)]
       [(> weight1 weight2) 
            (uf:reparent! uf root2 root1)]
       [else (write "this should be impossible")]
      )])
)) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions (i.e. private functions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; UFE = UnionFindEntry

; uf:reparent!: UFE UFE -> Void
; Sets the parent of `child` to be `parent` and makes corresponding adjustments to the parent's weight
(define (uf:reparent! uf child parent)
  (begin
   (set-UnionEntry-parent! (uf:get-entry uf child) parent)
   (set-UnionEntry-weight! (uf:get-entry uf parent) (+ (uf:get-weight uf parent)  (uf:get-weight uf child)))
  ))

; uf:get-entry: UF N -> UFE
; Gets the UFE in spot 'ix' from 'uf'.
(define (uf:get-entry uf ix)
  (vector-ref (UnionFind-data uf) ix))

; uf:get-parent: UF N -> N
; gets the parent of the UFE in spot 'ix' from 'uf'
(define (uf:get-parent uf ix)
 (UnionEntry-parent (uf:get-entry uf ix)))

; uf:get-weight: UF N -> N
; gets the weight of the UFE in spot 'ix' from 'uf'
(define (uf:get-weight uf ix)
  (UnionEntry-weight (uf:get-entry uf ix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 1B: Complete binary heap
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complete binary heap functions (i.e. public functions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-struct heap [size lt? data])

; heap:create : N [Order] -> Heap
; creates a heap structure of size capacity. As the heap is empty, all components of the heap 
; are initiliazed to #false
(define (heap:create capacity lt?)
  (make-heap 0 lt? (make-vector capacity #false)))

; heap:insert! : Heap X -> Void
; Adds new element to the end of the heap and then 'bubbles up' to restore
; the heap invariant.
(define (heap:insert! heap new-element)
  (local
    [(define oldSize (heap-size heap))]
    (cond
      [(> (+ (heap-size heap) 1) (vector-length (heap-data heap))) ;; expand if necessary
       (begin
         (expansion heap (heap-size heap))              ;; brand new heap
         (set-heap-size! heap (+ oldSize 1) )          
         (heap:set! heap (heap-size heap) new-element)  ;; add it to the end of the heap
         (heap:bubble-up! heap (heap-size heap) ) )]    ;; bubble it up
      [else                                             ;; do not need to expand
       (begin
         (set-heap-size! heap (+ (heap-size heap) 1) )
         (heap:set! heap (heap-size heap) new-element)  ;; add it to the end of the heap
         (heap:bubble-up! heap (heap-size heap) ) )]    ;; bubble it up
      )))

; heap:find-min : heap -> X
; Returns the smallest (according to the heap's order) element in the heap
; (which is at index 0)
(define (heap:find-min heap)
  (if (= (heap-size heap) 0) (error "the heap is empty") (heap:ref heap 1)))

; heap:remove-min! : heap -> void
; Removes the smallest element from the given heap
; Will throw an error if the heap is empty
(define (heap:remove-min! heap)
  (cond
  [(> (heap-size heap) 0)
    (begin
      (heap:set! heap 1 (heap:ref heap (heap-size heap))) ; step1 replace the root with the last node
      (set-heap-size! heap (- (heap-size heap) 1) )
      (heap:percolate-down! heap 1))]
   [else 
    (error "the heap is empty")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions (i.e. private functions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; heap:bubble-up! : heap N -> Void
; Restores the heap invariant by bubbling up the element at index 'index'.
(define (heap:bubble-up! heap index)
  (local
    [(define p1 (heap:parent index))]
    (if
       (and (and (> p1 0) (> index 1)) ((heap-lt? heap) (heap:ref heap index) (heap:ref heap p1)))
        (begin
            (heap:swap! heap index p1)
            (heap:bubble-up! heap p1))
       void)
))

; heap:find-smaller-child : heap N -> N
; Returns the index of the smaller child of the element at index 'index'.
; Will return #false if no children.
(define (heap:find-smaller-child heap index)
  (local
    [(define child1 (heap:left index))
     (define child2 (heap:right index))]
    (cond 
      [( < (heap-size heap) child1) #false]   ; no children
      [( = (heap-size heap) child1) child1]   ; only left child
      [else (if ((heap-lt? heap) (heap:ref heap child1) (heap:ref heap child2)) child1 child2)]
)))

; heap:lt? : heap N N -> Bool
; Is the heap element at index 'i' less than the heap element at index 'j'?
; (using the heap's order)
(define (heap:lt? heap i j)
  (if ((heap-lt? heap) (heap:ref heap i) (heap:ref heap j))  #true #false))

; heap:percolate-down! : heap N
; Restores the heap invariant by checking if the invariant holds, and swapping otherwise, starting with
; the element at index 0 in the heap
(define (heap:percolate-down! heap index)
  (local
    [(define smallerChild  (heap:find-smaller-child heap index))]
    (cond
      [(number? smallerChild) ; if no smaller child, smallerChild will be #false
       (cond
         [(and (and (> index 0) (or (< smallerChild (heap-size heap)) (= smallerChild (heap-size heap)) ) ) ((heap-lt? heap) (heap:ref heap smallerChild)  (heap:ref heap index)) )
          (begin
            (heap:swap! heap index smallerChild)
            (heap:percolate-down! heap smallerChild))]
         [else void])]
       [else void] )))

; heap:ref : heap N -> X
; Returns the element in the heap that is at index N
; NOTE: N is greater than or equal to 1
(define (heap:ref heap N)
    (vector-ref (heap-data heap) (- N 1)) ) ; other functions act like the first array index is 1, but racket implementation says first is index 0, so must adjust

; heap:set! : heap N R -> void
; Sets the heap element at index 'pos' to be 'val'
(define (heap:set! heap pos val)
   (vector-set! (heap-data heap) (- pos 1) val))  

; heap:swap! : heap N N -> void
; Swaps the heap element at position 'vert1' with the heap element at position 'vert2'
(define (heap:swap! heap vert1 vert2)
  (local
    [(define val1 (heap:ref heap vert1))
     (define val2 (heap:ref heap vert2))]
  (begin
    (heap:set! heap vert1 val2)
    (heap:set! heap vert2 val1)
)))

; heap:left : N -> N
; Returns the index of the left child of the given index
(define (heap:left i)
  (* 2 i))

; heap:right : N -> N
; Returns the index of the left child of the given index.
(define (heap:right i)
  (+ (* 2 i) 1))

; heap:parent : N -> N
; Returns the index of the parent of the given index.
(define (heap:parent i)
 (floor (/ i 2)))

; expansion: heap N -> void
; If expansion  is necessary, create twice as large heap and then take out values
; from inital and put them into the expanded heap.
(define (expansion heap N)
  (cond  
    [(> (+ N 1) (vector-length (heap-data heap)))
     (local
       [(define anotherHeap (heap:create (* (heap-size heap) 2) (heap-lt? heap)) )]
       (recursiveExpansion heap anotherHeap))]
    [else void]))

; recursiveExpansion : heap heap -> void
; Takes values out of initialHeap and puts them into expandedHeap (recursively)
(define (recursiveExpansion initialHeap expandedHeap)
  (cond
    [(> (heap-size initialHeap) 0)
     (begin
         (heap:insert! expandedHeap (heap:find-min initialHeap))
         (heap:remove-min! initialHeap)
         (recursiveExpansion initialHeap expandedHeap))]
    [else 
       (set-heap-data! initialHeap (heap-data expandedHeap))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PART 2: WEIGHTED, UNDIRECTED GRAPH API ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Vertex is a N+
;; Weight is a Real Number

;; MaybeWeight is either
;;   a real number   (corresponds to the weight of an edge) 
;;   +inf.0          (corresponds to no edge)

;; A WUGraph is represented using an adjacency matrix
(define-struct WUGraph (size adjMatrix))

;; make-graph : N -> WUGrap
;; Creates a new undirected, wieghted graph with n disjoint vertices (i.e. no edges)
;; Adjancency matrix is a vector of vectors, all initiliazed to +inf.0
(define (make-graph n)
   (make-WUGraph n  (build-vector n (lambda (index) (make-vector n +inf.0))) ))

;; graph-size : WUGraph -> N
;; Returns number of vertices in graph
;; Note: this will remain constant throughout the graph's life
(define (graph-size g)
  (WUGraph-size g))

;; get-edge: WUGraph N N -> MaybeWeight
;; Gives the weight of the edge from N1 to N2
;; (Note: if no edge exists, then will return infinity)
;; (Note: N N must be vertices in the graph)
(define (get-edge g v u)
 (vector-ref (vector-ref (WUGraph-adjMatrix g) u) v))

;; set-edge!: WUGraph N N N -> Void
;; sets the weight of the edge from 'u' to 'v' to be 'weight'
(define (set-edge! g u v weight)
  (begin
     ;; must change two spots in the table
     (vector-set! (vector-ref (WUGraph-adjMatrix g) u) v weight)
     (vector-set! (vector-ref (WUGraph-adjMatrix g) v) u weight)
))

;; get-adjacent: WUGraph N -> [List-of N]
;; Returns a list of all the vertices adjacent to vertex N
;; (Note: N must correspond to a vertex)
(define (get-adjacent g v)
  (local
    [(define procList '())
     (define unprocList (vector-ref (WUGraph-adjMatrix g) v))] 
  (begin
     ;; now need to filter out all the +inf.0 values
     (let again [(i 0)]
     (when (< i (graph-size g))
       (begin
         (if (= (vector-ref unprocList i) +inf.0)
             (void)
             (set! procList (cons i procList)) )
           (again (+ i 1))))) 
     (sort procList <))))

;; notInf : N -> Bool
;; If not infinity, returns true. Else returns false.
(define (notInf n)
  (not (= n +inf.0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 2B- Testing for undirected, unwieghted graph API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-struct testingCommand [command obj1 obj2 obj3])

; graph-testing-script! : Graph [List-of-testingCommand] -> [List-of-bools]
; Carries out a series of graph commands seqeuentially and returns a list of the return values.
(define (graph-testing-script! graph ListOfCommands)
  (begin
    (if (empty? ListOfCommands) '()
        (begin
          (local
            [(define currentCommand (first ListOfCommands))]
            (cond 
              [(symbol=? (testingCommand-command currentCommand) 'get-edge)
                (local
                  [(define currentResult (get-edge graph (testingCommand-obj1 currentCommand) (testingCommand-obj2 currentCommand)))]
                  (cons currentResult (graph-testing-script! graph (rest ListOfCommands)))
                  )]
              [(symbol=? (testingCommand-command currentCommand) 'get-adjacent)
                (local
                  [(define currentResult (get-adjacent graph (testingCommand-obj1 currentCommand)))]
                  (cons currentResult (graph-testing-script! graph (rest ListOfCommands))))]
              [(symbol=? (testingCommand-command currentCommand) 'set-edge)
                (begin
                  (set-edge! graph (testingCommand-obj1 currentCommand) (testingCommand-obj2 currentCommand) (testingCommand-obj3 currentCommand))
                  (graph-testing-script! graph (rest ListOfCommands)))]
))))))

(check-expect (graph-size (make-graph 5)) 5)

(check-expect 
 (graph-testing-script!
     (make-graph 5)
     (cons (make-testingCommand 'set-edge 0 1 2) 
     (cons (make-testingCommand 'set-edge 2 3 4) 
     (cons (make-testingCommand 'get-edge 0 1 #false) 
     (cons (make-testingCommand 'get-edge 2 3 #false) 
     (cons (make-testingCommand 'get-adjacent 1 #false #false) 
     '()))))))
 '(2 4 (0)) )

(check-expect 
 (graph-testing-script!
     (make-graph 5)
     (cons (make-testingCommand 'set-edge 0 1 2) 
     (cons (make-testingCommand 'set-edge 2 3 4)
     (cons (make-testingCommand 'set-edge 0 2 5) 
     (cons (make-testingCommand 'set-edge 0 3 6) 
     (cons (make-testingCommand 'set-edge 1 3 7) 
     (cons (make-testingCommand 'set-edge 4 3 8) 
     (cons (make-testingCommand 'set-edge 1 4 9) 
     (cons (make-testingCommand 'get-edge 0 1 #false) 
     (cons (make-testingCommand 'get-edge 0 3 #false) 
     (cons (make-testingCommand 'get-adjacent 1 #false #false) 
     '())))))))))))
 '(2 6 (0 3 4)) )

(check-expect 
 (graph-testing-script!
     (make-graph 10)
     (cons (make-testingCommand 'get-adjacent 1 #false #false)
     (cons (make-testingCommand 'set-edge 1 9 10) 
     (cons (make-testingCommand 'get-adjacent 1 #false #false) 
     (cons (make-testingCommand 'get-adjacent 9 #false #false) 
     (cons (make-testingCommand 'set-edge 2 7 5) 
     (cons (make-testingCommand 'set-edge 3 7 6)
     (cons (make-testingCommand 'set-edge 4 7 7)
     (cons (make-testingCommand 'get-adjacent 7 #false #false)
     '())))))))))
 '(() (9) (1) (2 3 4)) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PART 3: KRUSKAL’S ALGORITHM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; kruskal-mst : WUGraph -> WUGraph
;; Returns a minimum spanning tree of the input graph using Kruskal's algorithm
(define (kruskal-mst g)
  (local
     [(define ufKMST (uf:create (graph-size g))) ;; new graph with all the vertices and no edges
      (define edgLst (get-all-edges/increasing g))] ;; get list of edge-weights in sorted order
   (createWUG ufKMST edgLst (make-graph (graph-size g)))  ;; then add all the edge-weights to the new graph
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HELPER FUNCTIONS ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-struct edgesWeight (from to weight))
(define-struct unsortedEdges (size edges))

; edgesWeight-lt? : edgesWeight edgesWeight -> Bool
; Is the weight of edgeW1 greater than the weight of edgeW2?
(define (edgesWeight-lt? edgeW1 edgeW2)
  (> (edgesWeight-weight edgeW1) (edgesWeight-weight edgeW2)))

; createWUG : UF [List-of-edgesWeight] - > WUGraph
; Goes through the [List-of-edgesWeight], which are ordered from least to most 'costly'.
; If there is not already a connection between the edges, then connect them. Else, discard and
; move on.
(define (createWUG uf listOfTheEdges newWUG)
  (local
    [(define workingVertPar null)
     (define currEdge null)]
   (cond
     [(empty? listOfTheEdges) newWUG]
     [else 
       (begin
          (set! currEdge (first listOfTheEdges))
          (cond
             [(uf:same-set? uf (edgesWeight-from currEdge) (edgesWeight-to currEdge))  ; do nothing if in same set
              (createWUG uf (rest listOfTheEdges) newWUG)]                             ; if not empty, need to keep checking
             [else                                                                     ; if not connected, then connect
              (begin
                (uf:union! uf (edgesWeight-from currEdge) (edgesWeight-to currEdge))
                (set-edge! newWUG (edgesWeight-from currEdge) (edgesWeight-to currEdge) (edgesWeight-weight currEdge)) 
                (createWUG uf (rest listOfTheEdges) newWUG))] )
           )]
)))

; find-and-remove-min! : Heap -> X
; Stores minimum heap element in temporary variable. Removes min element
; from heap, then returns the temporary variable.
(define (find-and-remove-min! heap)
  (local
    [(define curMin (heap:find-min heap))]
 (begin
   (heap:remove-min! heap)
   curMin)
))

; get-all-edges : WUGraph -> unsortedEdges (which consists of N (size) and List-of-edgesWeight)
; Goes through the WUGraph, constructing an edgesWeight struct for each edge and then adding it
; to the unsortedEdges data struct, which is returned.
; Note: each edge is included only once (in only one (arbitrary) direction)
; Note: the [List-of-edgesWeight] inside the returned unsortedEdges data struct is unordered
(define (get-all-edges g)
 (local
  [(define ListoEdges '())
   (define listSize 0)    ]
 (begin
 (let again [(i 0)]
  (when (< i (graph-size g))
    (begin
     (let again2 [(j 0)]
       (when (< j (graph-size g))
         (begin
           (if (or (= i j) (< i j))
               (if (not (= (get-edge g i j) +inf.0))
                   (begin
                     (set! ListoEdges (cons  (make-edgesWeight i j (get-edge g i j)) ListoEdges))
                     (set! listSize (+ listSize 1)))
                   void)
              void)
               (again2 (+ j 1)))))
      (again (+ i 1)))))
      (make-unsortedEdges listSize ListoEdges))
))

; get-all-edges/increasing : WUGraph -> [List-of-edgesWeight]
; Returns a sorted list of all edges in the graph, from least to most weight,
; using the edgesWeight struct.
; Does this by first getting an unsorted list of the edges using the
; 'get-all-edges' function and then sorting that list using the 'heap-sort' function.
; Note: each edge is included only once (in only one (arbitrary) direction)
(define (get-all-edges/increasing g)
  (local
    [(define inProg (get-all-edges g))]
  (heap-sort edgesWeight-lt? inProg)))

; heap-sort : [Order] unsortedEdges -> [List-of-edgesWeight]
; Sorts the [List-of-edgesWeight] in the unsortedEdges data struct based 
; on the given ordering by adding all the values to a heap and then
; repeatedly removing the minimum value until the heap is empty.
(define (heap-sort lt? xs)
  (local
    [(define heapBeingSorted (heap:create (unsortedEdges-size xs) lt?))]
  (begin
    (heap-sort-recursive heapBeingSorted (unsortedEdges-edges xs))
    (heap-to-list heapBeingSorted '() )
)))

; heap-sort-recursive : Heap [List-of-edgesWeight] - > Heap
; Takes the first value in the list and adds it to the heap.
; Then uses recursion to go through the whole list.
(define (heap-sort-recursive heap listOfEdgesWeight)
  (if (not (empty? listOfEdgesWeight))
     (begin
        (heap:insert! heap (first listOfEdgesWeight))
        (heap-sort-recursive heap (rest listOfEdgesWeight))) 
      heap))

; heap-to-list : Heap List -> List
; Find and remove the min value in the heap. Add it to the return list.
; Repeat until the heap is empty.
(define (heap-to-list heap lst) 
 (local
   [(define workingList lst)]
 (begin
   (let again3 [(i (heap-size heap))]
     (when (< 0 i )
      (begin
        (set! workingList (cons (find-and-remove-min! heap) workingList))
     (again3 (- i 1)) )))
    workingList)
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unit testing for the helper functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-expect
 (edgesWeight-lt? (make-edgesWeight 0 1 4) (make-edgesWeight 1 2 1))
 #true)

; Returns the heaviest, which may seem a contradiction to the
; function declaration but it will make sense once all
; the code is examined
(check-expect
 (local
   [(define myheap (heap:create 10 edgesWeight-lt?))]
  (begin
      (heap:insert! myheap (make-edgesWeight 0 3 8))
      (heap:insert! myheap (make-edgesWeight 0 1 6))
      (heap:insert! myheap (make-edgesWeight 0 7 3))
      (find-and-remove-min! myheap)))
 (make-edgesWeight 0 3 8))

(check-expect
 (local
   [(define myheap (make-graph 5))]
   (begin
     (set-edge! myheap 0 1 10)
     (set-edge! myheap 0 2 20)
     (set-edge! myheap 3 4 30)   
     (get-all-edges/increasing myheap)))
 (list (make-edgesWeight 0 1 10)
       (make-edgesWeight 0 2 20)
       (make-edgesWeight 3 4 30)))

(check-expect 
 (heap-sort edgesWeight-lt? (make-unsortedEdges 4 (list (make-edgesWeight 0 1 4) (make-edgesWeight 2 3 6) (make-edgesWeight 4 5 2) (make-edgesWeight 4 2 1))))
 (list (make-edgesWeight 4 2 1) (make-edgesWeight 4 5 2) (make-edgesWeight 0 1 4) (make-edgesWeight 2 3 6)))

(check-expect 
 (local
   [(define testList  (list (make-edgesWeight 3 4 10) (make-edgesWeight 0 1 5) (make-edgesWeight 0 2 20)))
    (define testListWE (make-unsortedEdges 3 testList))]   
   (heap-sort edgesWeight-lt? testListWE))
 (list (make-edgesWeight 0 1 5)
       (make-edgesWeight 3 4 10)
       (make-edgesWeight 0 2 20)))

(check-expect 
 (local
   [(define extensiveTest (heap:create 10 edgesWeight-lt?))]
   (begin
     (heap:insert! extensiveTest (make-edgesWeight 0 1 5))
     (heap:insert! extensiveTest (make-edgesWeight 2 3 6))
     (heap:insert! extensiveTest (make-edgesWeight 4 5 7))
     (heap:insert! extensiveTest (make-edgesWeight 6 7 8))                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            
     (heap:insert! extensiveTest (make-edgesWeight 8 9 9))
     (heap:insert! extensiveTest (make-edgesWeight 0 9 10))
     (heap:insert! extensiveTest (make-edgesWeight 4 7 11))
     (heap:insert! extensiveTest (make-edgesWeight 1 4 12))
     (heap:insert! extensiveTest (make-edgesWeight 6 2 13))  
     (heap-to-list extensiveTest '()))) 
  (list (make-edgesWeight 0 1 5)
        (make-edgesWeight 2 3 6)
        (make-edgesWeight 4 5 7)
        (make-edgesWeight 6 7 8)
        (make-edgesWeight 8 9 9)
        (make-edgesWeight 0 9 10)
        (make-edgesWeight 4 7 11)
        (make-edgesWeight 1 4 12)
        (make-edgesWeight 6 2 13)))

(check-expect 
 (local
   [(define heap1 (heap:create 5 edgesWeight-lt?))]
   (begin
     (heap:insert! heap1 (make-edgesWeight 0 1 5))
     (heap:insert! heap1 (make-edgesWeight 3 4 10))
     (heap:insert! heap1 (make-edgesWeight 0 2 20))    
     (heap-to-list heap1 '())))
  (list (make-edgesWeight 0 1 5)
        (make-edgesWeight 3 4 10)
        (make-edgesWeight 0 2 20)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 3B- Testing for Kruskal's algorithm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; construct-graph : WUGraph [List-of [list Vert Vert Weight]] -> WUgraph
; Takes the given graph, adds all the listed edges, and then returns the resulting graph.
(define (construct-graph graph ListOfCommands)
    (if (empty? ListOfCommands) '()
          (local
              [(define currentCommand (first ListOfCommands))]
          (begin
            (set-edge! graph (first currentCommand) (second currentCommand) (third currentCommand))
            (construct-graph graph (rest ListOfCommands))
            graph))
           ))

;; Double check the graph API and the current graph-construction apparatus
(define EXAMPLE-GRAPH-J0
  (construct-graph (make-graph 10)
               '((0 9 20)
                 (0 8 30)
                 (0 7 40)
                 (1 6 7)
                 (1 2 12)
                 (5 8 10)
                 (8 9 0))))

(check-expect (graph-size EXAMPLE-GRAPH-J0) 10)
(check-expect (get-edge EXAMPLE-GRAPH-J0 0 9) 20)
(check-expect (get-edge EXAMPLE-GRAPH-J0 0 8) 30)
(check-expect (get-edge EXAMPLE-GRAPH-J0 0 7) 40)
(check-expect (get-edge EXAMPLE-GRAPH-J0 1 6) 7)
(check-expect (get-edge EXAMPLE-GRAPH-J0 1 2) 12)
(check-expect (get-edge EXAMPLE-GRAPH-J0 5 8) 10)
(check-expect (get-edge EXAMPLE-GRAPH-J0 8 9) 0)

(check-expect (= +inf.0 (get-edge EXAMPLE-GRAPH-J0 0 3)) #true)
(check-expect (= +inf.0 (get-edge EXAMPLE-GRAPH-J0 9 0)) #false)

(check-expect (get-adjacent EXAMPLE-GRAPH-J0 9) '(0 8))
(check-expect (get-adjacent EXAMPLE-GRAPH-J0 8) '(0 5 9))
(check-expect (get-adjacent EXAMPLE-GRAPH-J0 5) '(8))

(check-expect (get-all-edges/increasing EXAMPLE-GRAPH-J0) (list
                                                          (make-edgesWeight 8 9 0)
                                                          (make-edgesWeight 1 6 7)
                                                          (make-edgesWeight 5 8 10)
                                                          (make-edgesWeight 1 2 12)
                                                          (make-edgesWeight 0 9 20)
                                                          (make-edgesWeight 0 8 30)
                                                          (make-edgesWeight 0 7 40)))

;; Now start also testing Kruskal's algorithm in the construction of minimum spanning trees for graphs
(define EXAMPLE-GRAPH-J1
  (construct-graph (make-graph 9)
               '((0 1 8)
                 (0 2 12)
                 (2 1 13)
                 (3 2 14)
                 (1 3 25)
                 (2 6 21)
                 (3 6 12)
                 (6 8 11)
                 (8 3 16)
                 (3 7 12)
                 (7 8 9)
                 (3 5 8)
                 (5 7 11)
                 (3 4 20)
                 (4 5 19)
                 (1 4 9)
                 )))


(define EXAMPLE-MST-J1 (kruskal-mst EXAMPLE-GRAPH-J1))

(check-expect (get-all-edges/increasing EXAMPLE-GRAPH-J1) (list
                                                          (make-edgesWeight 0 1 8)
                                                          (make-edgesWeight 3 5 8)
                                                          (make-edgesWeight 1 4 9)
                                                          (make-edgesWeight 7 8 9)
                                                          (make-edgesWeight 5 7 11)
                                                          (make-edgesWeight 6 8 11)
                                                          (make-edgesWeight 3 6 12)
                                                          (make-edgesWeight 3 7 12)
                                                          (make-edgesWeight 0 2 12)
                                                          (make-edgesWeight 1 2 13)
                                                          (make-edgesWeight 2 3 14)
                                                          (make-edgesWeight 3 8 16)
                                                          (make-edgesWeight 4 5 19)
                                                          (make-edgesWeight 3 4 20)
                                                          (make-edgesWeight 2 6 21)
                                                          (make-edgesWeight 1 3 25)) )
                                                          
                                                         
(check-expect (get-adjacent EXAMPLE-MST-J1 0) '(1 2))
(check-expect (get-adjacent EXAMPLE-MST-J1 1) '(0 4))
(check-expect (get-adjacent EXAMPLE-MST-J1 2) '(0 3))
(check-expect (get-adjacent EXAMPLE-MST-J1 3) '(2 5))
(check-expect (get-adjacent EXAMPLE-MST-J1 4) '(1))
(check-expect (get-adjacent EXAMPLE-MST-J1 5) '(3 7))
(check-expect (get-adjacent EXAMPLE-MST-J1 6) '(8))
(check-expect (get-adjacent EXAMPLE-MST-J1 7) '(5 8))
(check-expect (get-adjacent EXAMPLE-MST-J1 8) '(6 7))

(define EXAMPLE-GRAPH-J2
  (construct-graph (make-graph 10)
               '((0 1 10)
                 (1 6 8)
                 (5 6 10)
                 (6 7 10)
                 (1 7 13)
                 (1 2 10)
                 (2 7 8)
                 (7 8 10)
                 (2 8 13)
                 (2 3 10)
                 (3 8 8)
                 (3 4 10)
                 (8 9 10)
                 )))


(check-expect (get-all-edges/increasing EXAMPLE-GRAPH-J2) (list
                                                           (make-edgesWeight 1 6 8)
                                                           (make-edgesWeight 2 7 8)
                                                           (make-edgesWeight 3 8 8)
                                                           (make-edgesWeight 5 6 10)
                                                           (make-edgesWeight 7 8 10)
                                                           (make-edgesWeight 0 1 10)
                                                           (make-edgesWeight 3 4 10)
                                                           (make-edgesWeight 2 3 10)
                                                           (make-edgesWeight 6 7 10)
                                                           (make-edgesWeight 8 9 10)
                                                           (make-edgesWeight 1 2 10)
                                                           (make-edgesWeight 1 7 13)
                                                           (make-edgesWeight 2 8 13)) )




(define EXAMPLE-MST-J2 (kruskal-mst EXAMPLE-GRAPH-J2))


(check-expect (get-adjacent EXAMPLE-MST-J2 0) (list 1))
(check-expect (get-adjacent EXAMPLE-MST-J2 1) (list 0 6))
(check-expect (get-adjacent EXAMPLE-MST-J2 2) (list 7))
(check-expect (get-adjacent EXAMPLE-MST-J2 3) (list 4 8))
(check-expect (get-adjacent EXAMPLE-MST-J2 4) (list 3))
(check-expect (get-adjacent EXAMPLE-MST-J2 5) (list 6))
(check-expect (get-adjacent EXAMPLE-MST-J2 6) (list 1 5 7))
(check-expect (get-adjacent EXAMPLE-MST-J2 7) (list 2 6 8))
(check-expect (get-adjacent EXAMPLE-MST-J2 8) (list 3 7 9))
(check-expect (get-adjacent EXAMPLE-MST-J2 9) (list 8))


(define EXAMPLE-GRAPH-J3
  (construct-graph (make-graph 5)
               '((0 3 13)
                 (0 1 24)
                 (0 4 22)
                 (0 2 13)
                 (2 3 19)
                 (2 1 22)
                 (2 4 14)
                 (1 4 13)
                 (4 3 19)
                 (1 3 13)
                 )))

(check-expect (get-all-edges/increasing EXAMPLE-GRAPH-J3) (list
                                                           (make-edgesWeight 0 3 13)
                                                           (make-edgesWeight 1 3 13)
                                                           (make-edgesWeight 1 4 13)
                                                           (make-edgesWeight 0 2 13)
                                                           (make-edgesWeight 2 4 14)
                                                           (make-edgesWeight 2 3 19)
                                                           (make-edgesWeight 3 4 19)
                                                           (make-edgesWeight 1 2 22)
                                                           (make-edgesWeight 0 4 22)
                                                           (make-edgesWeight 0 1 24)) )

(define EXAMPLE-MST-J3 (kruskal-mst EXAMPLE-GRAPH-J3))


(check-expect (get-adjacent EXAMPLE-MST-J3 0) (list 2 3))
(check-expect (get-adjacent EXAMPLE-MST-J3 1) (list 3 4))
(check-expect (get-adjacent EXAMPLE-MST-J3 2) (list 0))
(check-expect (get-adjacent EXAMPLE-MST-J3 3) (list 0 1))
(check-expect (get-adjacent EXAMPLE-MST-J3 4) (list 1))
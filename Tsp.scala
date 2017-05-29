/**
  * Travelling salesman problem tomfoolery.
  *   Nodes are represented by integers [0,N).
  *   Distances are represented by a distance metric fn.
  */
case class TspConfig(N: Int, d: (Int, Int) => Double) {
  def length(path: Seq[Int]): Double = length(Path(path))
  def length(path: Path): Double = path.length(d)

  def shorterPath(p1: Seq[Int], p2: Seq[Int]): Seq[Int] = {
    if(length(p1) <= length(p2)) p1 else p2
  }
}

case class Path(nodes: Seq[Int]) {
  def edges: Seq[(Int, Int)] = nodes.zip(nodes.tail)

  def length(d: (Int, Int) => Double): Double = edges.foldLeft(0.0) { (partLen, edge) => partLen + d(edge._1, edge._2) }
}

case class ArrayMetric(a: Array[Array[Double]]) {
  // Metric function
  def d(n1: Int, n2: Int) = a(n1)(n2)
}

object MetricUtils {
  val r = new util.Random

  /**
    *  Generate a random distance function, with edges in [0.0, 1.0)
    */
  def random(N: Int): (Int, Int) => Double = {
    // Generate a random NxN array
    val a = Array.fill(N, N) { r.nextDouble }
    // Zero out d(i,i)
    (0 to N-1).foreach { i => a(i)(i) = 0.0 }
    ArrayMetric(a).d
  }
}

object Tsp {
  /**
    *  Generate all Hamiltonian cycles, starting and ending at node 0
    */
  def hamCycles(N: Int): Iterator[Seq[Int]] = {
    (1 to N-1).permutations.map { path => Seq(0) ++ path ++ Seq(0) }
  }

  def avgHamCycle(tsp: TspConfig): Double = {
    hamCycles(tsp.N).foldLeft(0.0) { (sum, cycle) =>
      sum + tsp.length(cycle)
    } / hamCycles(tsp.N).size
  }

  /**
    * Find the shortest cycle by brute force.
    */
  def minHamCycle(tsp: TspConfig): Seq[Int] = {
    hamCycles(tsp.N).reduceLeft(tsp.shorterPath)
  }

  /**
    *  Greedy cycle starting at the given node
    */
  def greedyHamCycle(tsp: TspConfig, n0: Int = 0): Seq[Int] = {
    var i = n0
    var nodesLeft = (0 to tsp.N-1).toSet - i
    var path = Seq(i)
    while(nodesLeft.nonEmpty) {
      // Shortest next edge
      val j = nodesLeft.reduceLeft { (n1, n2) =>
        // println(s"        from $i: $i->$n1 = ${tsp.d(i, n1)} vs $i->$n2 = ${tsp.d(i, n2)}")
        if(tsp.d(i, n1) <= tsp.d(i, n2)) n1 else n2
      }
      // println(s"    best was $i -> $j")
      i = j
      nodesLeft = nodesLeft - i
      path = path :+ i
    }
    // Complete the cycle
    path ++ Seq(n0)
  }

  /**
    *  Best greedy cycle starting at any node
    */
  def bestGreedyHamCycle(tsp: TspConfig): Seq[Int] = {
    (0 to tsp.N-1).map { n => greedyHamCycle(tsp, n) }.reduceLeft(tsp.shorterPath)
  }


  /**
    * DP approach to TSP.
    * Iteration 0 starts with all edges (0,j).
    * Iteration M computes the shortest path for each set of size M of internal nodes, and each end-point end-point j.
    *   This can be computed from the tableau of iteration M-1.
    * Iteration N-1 gives us the shorted paths from 0 to all i, passing through all nodes.
    * We can then trivially find the shortest cycle by adding the edge back to node 0 for all paths.
    */
  def dpMinHamCycle(tsp: TspConfig): Seq[Int] = {
    import scala.collection.mutable.{Map => MMap}

    // map: (internal-node-set, end-node k) -> shortest path (from node 0)
    var tab: MMap[(Set[Int], Int), Seq[Int]] = {
      var tab0: MMap[(Set[Int], Int), Seq[Int]] = MMap()
      var emptySet: Set[Int] = Set()
      for(k <- 1 to tsp.N-1) {
        tab0((emptySet, k)) = Seq(0, k)
      }
      tab0
    }
    // M is the size of the set of interior nodes of each path
    for(M <- 1 to tsp.N-2) {
      val tabM: MMap[(Set[Int], Int), Seq[Int]] = MMap()
      for(k <- 1 to tsp.N-1) {
        // Generate all combinations of interior point of length M, excluding node k
        val interiorNodes = (1 to k-1) ++ (k+1 to tsp.N-1)
        interiorNodes.combinations(M).map(_.toSet).foreach { nodeSet =>
          var minPathToKViaNodeset: Seq[Int] = Seq()
          var minPathLength = Double.MaxValue
          for(n <- nodeSet) {
            val intNodesWithoutN = nodeSet - n
            val minPathToN = tab((intNodesWithoutN, n))
            val lengthToK = tsp.length(minPathToN) + tsp.d(n, k)
            if(lengthToK < minPathLength) {
              minPathToKViaNodeset = minPathToN :+ k
              minPathLength = lengthToK
            }
          }
          // Install into new tableau
          tabM((nodeSet, k)) = minPathToKViaNodeset
        }
      }
      // Finished this step, next...
      tab = tabM
    }
    // Now we have the shortest paths from 0 to any i through all nodes.
    // Find the best hamilton cycle by closing the loop to 0 and finding the shortest.
    //println(s"tab N is $tab")
    var minCycle: Seq[Int] = (0 to tsp.N-1) :+ 0
    for((k, v) <- tab) {
      val cycle = v :+ 0
      if(tsp.length(cycle) < tsp.length(minCycle)) {
        minCycle = cycle
      }
    }
    minCycle
  }

  def time[A](work: => A): A = {
    val startMs = System.currentTimeMillis
    try {
      work
    }
    finally {
      val endMs = System.currentTimeMillis
      println(s"[${endMs-startMs}ms]")
    }
  }

  def main(args: Array[String]): Unit = {
    println("Hello, world!")
  }

  val MaxNForAvg = 10
  val MaxNForBrute = 10
  val MaxNForDp = 25
  val MaxNForGreedy = 1000

  def c(n1: Int, n2: Int) = 1.0

  // println("Constant d(i,j) = 1.0")
  // hamCycles(N).foreach { p =>
  //   val len = Path(p).length(c)
  //   println(s"$p => length $len")
  // }
  // val cAvg = avgHamCycle(TspConfig(N, c))
  // val cMin = minHamCycle(TspConfig(N, c))
  // val cMinLen = Path(cMin).length(c)
  // println(s"   min $cMin -> $cMinLen, avg $cAvg")

  // println()

  println("Random d(i,j)")

  for(N <- 1 to 25) {
    println(s"----------------- N = $N --------------------")
    for (i <- 1 to 2) {
      println()
      val tsp = TspConfig(N, MetricUtils.random(N))
      if(N <= MaxNForAvg) time {
        val dAvg = avgHamCycle(tsp)
        println(f"   avg     $dAvg%.6f")
      }
      if(N <= MaxNForBrute) time {
        val dMin = minHamCycle(tsp)
        val dMinLen = tsp.length(dMin)
        println(f"   min     $dMin -> $dMinLen%.6f")
      }
      if(N <= MaxNForDp) time {
        val dDpMin = dpMinHamCycle(tsp)
        val dDpMinLen = tsp.length(dDpMin)
        println(f"   dpMin   $dDpMin -> $dDpMinLen%.6f")
      }
      if(N <= MaxNForGreedy) time {
        val dGreedy = greedyHamCycle(tsp)
        val dGreedyLen = tsp.length(dGreedy)
        println(f"   greedy  $dGreedy -> $dGreedyLen%.6f")
      }
      if(N <= MaxNForGreedy) time {
        val dBestGreedy = bestGreedyHamCycle(tsp)
        val dBestGreedyLen = tsp.length(dBestGreedy)
        println(f"   greedyN $dBestGreedy -> $dBestGreedyLen%.6f")
      }
    }
    println()
  }
}

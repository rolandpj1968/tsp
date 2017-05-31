/**
  * Travelling salesman problem tomfoolery.
  *   Nodes are represented by integers [0,N).
  *   Edges are represented by a distance fn.
  */
case class Tsp(N: Int, d: (Int, Int) => Double) {
  def edges(path: Seq[Int]): Seq[(Int, Int)] = path.zip(path.tail)

  def length(path: Seq[Int]): Double = edges(path).map { case (n1, n2) => d(n1, n2) }.sum

  /**
    *  Generate all Hamiltonian cycles, starting and ending at node 0
    */
  def hamCycles: Iterator[Seq[Int]] = {
    (1 to N-1).permutations.map { path => Seq(0) ++ path ++ Seq(0) }
  }

  def avgHamCycle: Double = hamCycles.map(length).sum / hamCycles.size

  /**
    * Find the shortest cycle by brute force.
    */
  def bruteMinHamCycle: Seq[Int] = hamCycles.minBy(length)

  /**
    *  Greedy cycle starting at the given node
    */
  def greedyHamCycle(n0: Int = 0): Seq[Int] = {
    var i = n0
    var nodesLeft = (0 to N-1).toSet - i
    var path = Seq(i)
    while(nodesLeft.nonEmpty) {
      // Shortest next edge
      val j = nodesLeft.minBy { n => d(i, n) }
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
  def bestGreedyHamCycle: Seq[Int] = {
    (0 to N-1).map { n => greedyHamCycle(n) }.minBy(length)
  }

  /**
    * DP approach to TSP.
    * Iteration 0 starts with all edges (0,j).
    * Iteration M computes the shortest path for each set of size M of internal nodes, and each end-point end-point j.
    *   This can be computed from the tableau of iteration M-1.
    * Iteration N-1 gives us the shorted paths from 0 to all i, passing through all nodes.
    * We can then trivially find the shortest cycle by adding the edge back to node 0 for all paths.
    */
  def dpMinHamCycle: Seq[Int] = {
    val dpTab0 = (1 to N-1).map { k => (Set.empty[Int], k) -> Seq(0, k) }.toMap

    // DP iterations - M is the size of the set of interior nodes of each path
    val dpTab = (1 to N-2).foldLeft(dpTab0) { (dpTabM, M) =>
      (1 to N-1).map { k =>
        // Generate all combinations of nodes of length M, excluding node k
        val nodesNotK = (1 to k-1) ++ (k+1 to N-1)
        nodesNotK.combinations(M).map(_.toSet).map { comboM =>
          // Choose the best path through comboM to k by iterating over paths to the node before k
          (comboM, k) -> comboM.map { j => dpTabM(comboM-j, j) :+ k }.minBy(length)
        }
      }.flatten.toMap
    }

    // Now we have the shortest paths from 0 to any i through all (other) nodes.
    // Find the best hamilton cycle by closing the loop to 0 and finding the shortest one.
    dpTab.values.map(_ :+ 0).minBy(length)
  }
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

  for(N <- 2 to 25) {
    println(s"----------------- N = $N --------------------")
    for (i <- 1 to 2) {
      println()
      val tsp = Tsp(N, MetricUtils.random(N))
      if(N <= MaxNForAvg) time {
        val dAvg = tsp.avgHamCycle
        println(f"   avg     $dAvg%.6f")
      }
      if(N <= MaxNForBrute) time {
        val dMin = tsp.bruteMinHamCycle
        val dMinLen = tsp.length(dMin)
        println(f"   min     $dMin -> $dMinLen%.6f")
      }
      if(N <= MaxNForDp) time {
        val dDpMin = tsp.dpMinHamCycle
        val dDpMinLen = tsp.length(dDpMin)
        println(f"   dpMin   $dDpMin -> $dDpMinLen%.6f")
      }
      if(N <= MaxNForGreedy) time {
        val dGreedy = tsp.greedyHamCycle()
        val dGreedyLen = tsp.length(dGreedy)
        println(f"   greedy  $dGreedy -> $dGreedyLen%.6f")
      }
      if(N <= MaxNForGreedy) time {
        val dBestGreedy = tsp.bestGreedyHamCycle
        val dBestGreedyLen = tsp.length(dBestGreedy)
        println(f"   greedyN $dBestGreedy -> $dBestGreedyLen%.6f")
      }
    }
    println()
  }
}

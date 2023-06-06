package edu.yu.da;

/** Defines the API for specifying and solving the OverfullGranaries problem
 * (see the requirements document).
 *
 * Students MAY NOT change the public API of this class, nor may they add ANY
 * constructor.

 * @author Avraham Leff
 */


import java.util.*;

public class OverfullGranaries {
    /**
     * code for FlowEdge, FlowNetwork and FordFulkerson is based on code from Robert Sedgewick
     * the original code can be found here: https://algs4.cs.princeton.edu/64maxflow/FordFulkerson.java
     * here: https://algs4.cs.princeton.edu/64maxflow/FlowEdge.java.html
     * and here: https://algs4.cs.princeton.edu/code/edu/princeton/cs/algs4/FlowNetwork.java
     * I edited these classes, adapting them to suit this problem, and tweaking the code to conform to what I need,
     * but they are based on the classes found at the above links
     */
    class FlowEdge {
        private final int v;             // from
        private final int w;             // to
        private final int capacity;   // capacity
        private int flow;             // flow
        public FlowEdge(int v, int w, int capacity) {
            this.v=v;
            this.w=w;
            this.capacity=capacity;
            this.flow=0;
        }
        public int from() {return v;}
        public int to() {return w;}
        public int capacity() {return capacity;}
        public int flow() {return flow;}
        public int other(int vertex) {
            if      (vertex == v) return w;
            else if (vertex == w) return v;
            else throw new IllegalArgumentException("invalid endpoint");
        }
        /**
         * Returns the residual capacity of the edge in the direction
         *  to the given {@code vertex}.
         * @param vertex one endpoint of the edge
         * @return the residual capacity of the edge in the direction to the given vertex
         *   If {@code vertex} is the tail vertex, the residual capacity equals
         *   {@code capacity() - flow()}; if {@code vertex} is the head vertex, the
         *   residual capacity equals {@code flow()}.
         * @throws IllegalArgumentException if {@code vertex} is not one of the endpoints of the edge
         */
        public int residualCapacityTo(int vertex) {
            if      (vertex == v) return flow;              // backward edge
            else if (vertex == w) return capacity - flow;   // forward edge
            else throw new IllegalArgumentException("invalid endpoint");
        }

        /**
         * Increases the flow on the edge in the direction to the given vertex.
         * If {@code vertex} is the tail vertex, this increases the flow on the edge by {@code delta};
         * if {@code vertex} is the head vertex, this decreases the flow on the edge by {@code delta}.
         * @param vertex one endpoint of the edge
         * @param delta amount by which to increase flow
         * @throws IllegalArgumentException if {@code vertex} is not one of the endpoints
         *         of the edge
         * @throws IllegalArgumentException if {@code delta} makes the flow
         *         on the edge either negative or larger than its capacity
         * @throws IllegalArgumentException if {@code delta} is {@code NaN}
         */
        public void addResidualFlowTo(int vertex, int delta) {
            if (!(delta >= 0)) throw new IllegalArgumentException("Delta must be non-negative");
            if      (vertex == v) flow -= delta;           // backward edge
            else if (vertex == w) flow += delta;           // forward edge
        }
    }
    class FlowNetwork {
        private int V;
        private int E;
        private List<FlowEdge>[] adj;
        /**
         * Initializes an empty flow network with {@code V} vertices and 0 edges.
         * @param V the number of vertices
         * @throws IllegalArgumentException if {@code V < 0}
         */
        public FlowNetwork(int V) {
            if (V < 0) throw new IllegalArgumentException("Number of vertices in a Graph must be non-negative");
            this.V = V;
            this.E = 0;
            adj = (List<FlowEdge>[]) new ArrayList[V];
            for (int v = 0; v < V; v++)
                adj[v] = new ArrayList<>();
        }
        public int V() {return V;}
        public int E() {return E;}
        public void addEdge(FlowEdge e) {
            int v = e.from();
            int w = e.to();
            adj[v].add(e);
            adj[w].add(e);
            E++;
        }
        public Iterable<FlowEdge> adj(int v) {
            return adj[v];
        }
        // return list of all edges - excludes self loops
        public Iterable<FlowEdge> edges() {
            List<FlowEdge> list = new ArrayList<>();
            for (int v = 0; v < V; v++)
                for (FlowEdge e : adj(v)) {
                    if (e.to() != v)
                        list.add(e);
                }
            return list;
        }
    }
    class FordFulkerson {
        private boolean[] marked;     // marked[v] = true iff s->v path in residual graph
        private FlowEdge[] edgeTo;    // edgeTo[v] = last edge on shortest residual s->v path
        private int value=0;         // current value of max flow
        /**
         * @param G the flow network
         * @param s the source vertex
         * @param t the sink vertex
         */
        public FordFulkerson(FlowNetwork G, int s, int t) {
            while (hasAugmentingPath(G, s, t)) {
                // compute bottleneck capacity
                int bottle = Integer.MAX_VALUE;
                for (int v = t; v != s; v = edgeTo[v].other(v)) {
                    bottle = Math.min(bottle, edgeTo[v].residualCapacityTo(v));
                }
                // augment flow
                for (int v = t; v != s; v = edgeTo[v].other(v)) {
                    edgeTo[v].addResidualFlowTo(v, bottle);
                }
                value += bottle;
            }
        }
        public int value() {
            return value;
        }
        public boolean inCut(int v) {
            return marked[v];
        }
        //must be called before getMarkedFromSpecificVertexNotSource is ever invoked or results will be undefined
        public boolean[] getMarkedAfterFordFulkersonBeforeBFSCalledFromSpecificVertex(){return this.marked;}
        //must be called after getMarked if you want getMarked to have the right values
        public boolean[] getMarkedFromSpecificVertexNotSource(FlowNetwork G,int vertex, int t){
            hasAugmentingPath(G,vertex,t);
            return this.getMarkedAfterFordFulkersonBeforeBFSCalledFromSpecificVertex();
        }
        // is there an augmenting path?
        // if so, upon termination edgeTo[] will contain a parent-link representation of such a path
        // this implementation finds a shortest augmenting path (fewest number of edges),
        // which performs well both in theory and in practice
        private boolean hasAugmentingPath(FlowNetwork G, int s, int t) {
            edgeTo = new FlowEdge[G.V()];
            marked = new boolean[G.V()];
            // breadth-first search
            Queue<Integer> queue = new LinkedList<>();
            queue.add(s);
            marked[s] = true;
            while (!queue.isEmpty() && !marked[t]) {
                int v = queue.remove();
                for (FlowEdge e : G.adj(v)) {
                    int w = e.other(v);
                    // if residual capacity from v to w
                    if (e.residualCapacityTo(w) > 0 && !marked[w]) {
                        edgeTo[w] = e;
                        marked[w] = true;
                        queue.add(w);
                    }
                }
            }
            // is there an augmenting path?
            return marked[t];
        }
        // return excess flow at vertex v
        private int excess(FlowNetwork G, int v) {
            int excess = 0;
            for (FlowEdge e : G.adj(v)) {
                if (v == e.from()) excess -= e.flow();
                else excess += e.flow();
            }
            return excess;
        }

        // return excess flow at vertex v
        private boolean isFeasible(FlowNetwork G, int s, int t) {
            // check that net flow into a vertex equals zero, except at source and sink
            if (Math.abs(value + excess(G, s)) > 0) {
                System.err.println("Excess at source = " + excess(G, s));
                System.err.println("Max flow         = " + value);
                return false;
            }
            if (Math.abs(value - excess(G, t)) > 0) {
                System.err.println("Excess at sink   = " + excess(G, t));
                System.err.println("Max flow         = " + value);
                return false;
            }
            for (int v = 0; v < G.V(); v++) {
                if (v == s || v == t) continue;
                else if (Math.abs(excess(G, v)) > 0) {
                    System.err.println("Net flow out of " + v + " doesn't equal zero");
                    return false;
                }
            }
            return true;
        }

        // check optimality conditions
        private boolean check(FlowNetwork G, int s, int t) {
            // check that flow is feasible
            if (!isFeasible(G, s, t)) {
                System.err.println("Flow is infeasible");
                return false;
            }
            // check that s is on the source side of min cut and that t is not on source side
            if (!inCut(s)) {
                System.err.println("source " + s + " is not on source side of min cut");
                return false;
            }
            if (inCut(t)) {
                System.err.println("sink " + t + " is on source side of min cut");
                return false;
            }
            // check that value of min cut = value of max flow
            int mincutValue = 0;
            for (int v = 0; v < G.V(); v++) {
                for (FlowEdge e : G.adj(v)) {
                    if ((v == e.from()) && inCut(e.from()) && !inCut(e.to()))
                        mincutValue += e.capacity();
                }
            }
            if (Math.abs(mincutValue - value) > 0) {
                System.err.println("Max flow value = " + value + ", min cut value = " + mincutValue);
                return false;
            }
            return true;
        }
    }
    public class InitialEntryPreMappingStringToInt{
        private String from;
        private String to;
        private int capacity;
        public InitialEntryPreMappingStringToInt(String from, String to, int capacity){
            this.from=from;
            this.to=to;
            this.capacity=capacity;
        }
        public String getFrom(){return this.from;}
        public String getTo(){return this.to;}
        public int getCapacity(){return this.capacity;}
    }
    public final static double BUSHELS_TO_MOVE = 10_000;
    private List<InitialEntryPreMappingStringToInt> edgesToMap;
    private Map<String,Integer> StringToIntegerMapping;
    private Map<Integer,String> IntegerToStringMapping;
    private Set<String> vertices;
    private String[] x;
    private String[] y;
    boolean solved=false;
    private FlowNetwork g;
    private FordFulkerson ff;
    private int V;
    /** Constructor.
     *
     * @param X labelling of the overfull granaries, must contain at least one
     * element and no duplicates.  No element of X can be an element of Y.
     * @param Y labelling of the underfull granaries, must contain at least one
     * element and no duplicates.  No element of Y can be an element of X.
     */
    public OverfullGranaries(final String[] X, final String[] Y) {
        this.edgesToMap= new ArrayList<>();
        this.StringToIntegerMapping=new HashMap<>();
        this.IntegerToStringMapping=new HashMap<>();
        this.vertices=new HashSet<>();
        this.x=X;
        this.y=Y;
        for(String x: X){this.vertices.add(x);}
        for(String y:Y){this.vertices.add(y);}
    }

    /** Specifies that an edge exists from the specified src to the specified
     * dest of specified capacity.  It is legal to invoke edgeExists between
     * nodes in X, between nodes in Y, from a node in X to a node in Y, or for
     * src and dest to be hitherto unknown nodes.  The method cannot specify a
     * node in Y to be the src, nor can it specify a node in X to be the dest.
     *
     * @param src must contain at least one character
     * @param dest must contain at least one character, can't equal src
     * @param capacity must be greater than 0, and is specified implicitly to be
     * "bushels per hour"
     */
    public void edgeExists(final String src, final String dest, final int capacity)
    {
        this.vertices.add(src);
        this.vertices.add(dest);
        this.edgesToMap.add(new InitialEntryPreMappingStringToInt(src,dest,capacity));
    }
    /** Solves the OverfullGranaries problem.
     *
     * @return the minimum number hours neeed to achieve the goal of moving
     * BUSHELS_TO_MOVE number of bushels from the X granaries to the Y granaries
     * along the specified road map.
     * @note clients may only invoke this method after all relevant edgeExists
     * calls have been successfully invoked.
     */
    public double solveIt() {
        this.solved=true;
        this.V=vertices.size()+2;;
        this.StringToIntegerMapping.put("Noam",0);
        this.StringToIntegerMapping.put("Mayerfeld",V-1);
        this.IntegerToStringMapping.put(0,"Noam");
        this.IntegerToStringMapping.put(V-1,"Mayerfeld");
        int counter=1;
        for(String vertice:this.vertices){
            if(counter>V-1){throw new IllegalStateException("error creating mappings - more vertices than space in graph");}
            this.StringToIntegerMapping.put(vertice,counter);
            this.IntegerToStringMapping.put(counter,vertice);
            counter++;
        }
        this.g=new FlowNetwork(V);
        for(InitialEntryPreMappingStringToInt I: this.edgesToMap){
            int from=this.StringToIntegerMapping.get(I.getFrom());
            int to=this.StringToIntegerMapping.get(I.getTo());
            int capacity=I.getCapacity();
            this.g.addEdge(new FlowEdge(from,to,capacity));
        }
        for(String s:this.x){
            int from=0;
            int to=this.StringToIntegerMapping.get(s);
            this.g.addEdge(new FlowEdge(from,to,Integer.MAX_VALUE));
        }
        for(String s:this.y){
            int from=this.StringToIntegerMapping.get(s);
            int to=V-1;
            this.g.addEdge(new FlowEdge(from,to,Integer.MAX_VALUE));
        }
        this.ff=new FordFulkerson(g,0,V-1);
        if(this.ff.value==0){return Double.POSITIVE_INFINITY;}
        return 10000.0/this.ff.value();
    }

    /** Return the names of all vertices in the X side of the min-cut, sorted by
     * ascending lexicographical order.
     *
     * @return only the names of the vertices in the X side of the min-cut
     * @note clients may only invoke this method after solveIt has been
     * successfully invoked.  Else throw an ISE.
     */
    public List<String> minCut() {
        if(!this.solved){throw new IllegalStateException("tried to invoke minCut() before solveIt()");}
        if(this.ff.value()==0){return new ArrayList<>();}
        Set<String> mc=new HashSet<>();
        for(String s: this.x){
            mc.add(s);
            boolean[] reachableFromS=this.ff.getMarkedFromSpecificVertexNotSource(this.g,this.StringToIntegerMapping.get(s),this.V-1);
            for(int i=0;i<reachableFromS.length;i++){
                if(reachableFromS[i]){mc.add(this.IntegerToStringMapping.get(i));}
            }
        }
        mc.remove("Noam");
        mc.remove("Mayerfeld");
        List<String> results=new ArrayList<>();
        for(String s :mc){results.add(s);}
        Collections.sort(results);
        return results;
    }

} // OverfullGranaries

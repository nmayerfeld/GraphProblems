package edu.yu.da;

/** Defines the API for specifying and solving the FindDinner problem (see the
 * requirements document).  Also defines an inner interface, and uses it as
 * part of the ArithmeticPuzzleI API definition.
 *
 * Students MAY NOT change the public API of this class, nor may they add ANY
 * constructor.
 *
 * @author Avraham Leff
 */

import java.util.*;

public class FindDinner {
    public class Edge implements Comparable<Edge>{
        private int v;
        private int w;
        private int weight;
        public Edge(int v, int w, int weight){
            this.v=v;
            this.w=w;
            this.weight=weight;
        }
        public int weight(){
            return this.weight;
        }
        public int either(){
            return this.v;
        }
        public int other(int vertex){
            if(vertex==v) return this.w;
            else if(vertex==w) return this.v;
            else {
                throw new IllegalArgumentException("wrong edge vertices");
            }
        }
        @Override
        public int compareTo(Edge other){
            if(this.weight<other.weight()){
                return -1;
            }
            else if (this.weight>other.weight()){
                return +1;
            }
            else {
                return 0;
            }
        }
    }
    public class UndirectedEdgeWeightedGraph {
        private int V;
        private int E;
        private List<Edge>[] adj;
        public UndirectedEdgeWeightedGraph(int v){
            this.V=v;
            this.E=0;
            this.adj=(List<Edge>[]) new List[v];
            for(int i=0;i<v;i++){
                adj[i]=new ArrayList<Edge>();
            }
        }
        public int V() {return this.V;}
        public int E() {return this.E;}
        public void addEdge(Edge E){
            int v = E.either(), w=E.other(v);
            adj[v].add(E);
            adj[w].add(E);
            this.E++;
        }
        public Iterable<Edge> adj(int v){
            return this.adj[v];
        }
        public Iterable<Edge> edges(){
            List<Edge>list =new ArrayList<>();
            for(int v=0;v<this.V;v++){
                for(Edge e: adj[v]){
                    if(e.other(v)>v){
                        list.add(e);
                    }
                }
            }
            return list;
        }
    }
    public class IndexMinPQ<Key extends Comparable<Key>>{ //source: https://algs4.cs.princeton.edu/24pq/IndexMinPQ.java.html
        private int maxN;
        private int n;
        private int[]pq;
        private int[] qp;
        private Key[] keys;

        public IndexMinPQ(int maxN){
            if(maxN<0) throw new IllegalArgumentException();
            this.maxN=maxN;
            n=0;
            keys=(Key[])new Comparable[maxN+1];
            pq=new int[maxN+1];
            qp=new int[maxN+1];
            for(int i=0;i<=maxN;i++){
                qp[i]=-1;
            }
        }
        public boolean isEmpty(){
            return n==0;
        }
        public boolean contains(int i){
            validateIndex(i);
            return qp[i]!=-1;
        }
        public int size(){
            return n;
        }
        public void insert(int i, Key key){
            validateIndex(i);
            if(contains(i)) throw new IllegalArgumentException("index is already in the priority queue");
            n++;
            qp[i]=n;
            pq[n]=i;
            keys[i]=key;
            swim(n);
        }
        public int delMin(){
            if(n==0) throw new NoSuchElementException("priority queue underflow");
            int min=pq[1];
            exch(1,n--);
            sink(1);
            assert min==pq[n+1];
            qp[min]=-1;
            keys[min]=null;
            pq[n+1]=-1;
            return min;
        }
        public void changeKey(int i,Key key){
            validateIndex(i);
            if(!contains(i)) throw new NoSuchElementException("index is not in priority queue");
            keys[i]=key;
            swim(qp[i]);
            sink(qp[i]);
        }
        private void validateIndex(int i){
            if(i<0) throw new IllegalArgumentException("index is negative: "+i);
            if(i>=maxN) throw new IllegalArgumentException("index >= capacity: "+i);
        }
        private boolean greater(int i,int j){
            return keys[pq[i]].compareTo(keys[pq[j]])>0;
        }
        private void exch(int i, int j){
            int swap=pq[i];
            pq[i]=pq[j];
            pq[j]=swap;
            qp[pq[i]]=j;
            qp[pq[j]]=i;
        }
        private void swim(int k){
            while(k>1 && greater(k/2,k)){
                exch(k,k/2);
                k=k/2;
            }
        }
        private void sink(int k){
            while(2*k<=n){
                int j=2*k;
                if(j<n &&greater(j,j+1)) j++;
                if(!greater(k,j)) break;
                exch(k,j);
                k=j;
            }
        }
    }
    private UndirectedEdgeWeightedGraph g;
    private Edge[] sourceSPTEdgeTo;
    private int[] sourceSPTDistTo;
    private int[] sourceSPTNumNonDinnerPathsToVertex;
    private int[] sourceSPTNumYesDinnerPathsToVertex;
    private IndexMinPQ<Integer> sourceSPTPQ;
    private Edge[] destSPTEdgeTo;
    private int[] destSPTDistTo;
    private IndexMinPQ<Integer> destSPTPQ;
    private IndexMinPQ<Integer> thirdSPTPQ;
    private Edge[] thirdSPTEdgeTo;
    private int[] thirdSPTDistTo;
    private HashSet<Integer> citiesWithDinner;
    private boolean invokedSolveIt=false;
    private boolean shiftedNumberOfDinnerPathsAwayFromThisVertex=false;
    private int numShortestPathsWithDinner=0;
    private int lengthOfShortestPath=Integer.MAX_VALUE;
    /** Constructor: clients specify the number of cities involved in the
     * problem.  Cities are numbered 1..n, and for convenience, the "start" city
     * is labelled as "1", and the goal city is labelled as "n".
     *
     * @param nCities number of cities, must be greater than 1.
     */
    public FindDinner(final int nCities) {
        if(nCities<=1){
            throw new IllegalArgumentException("nCities<=1");
        }
        this.g=new UndirectedEdgeWeightedGraph(nCities);
        this.sourceSPTEdgeTo=new Edge[g.V()];
        this.sourceSPTDistTo=new int[g.V()];
        this.sourceSPTNumNonDinnerPathsToVertex=new int[g.V()];
        this.sourceSPTNumYesDinnerPathsToVertex=new int[g.V()];
        this.sourceSPTPQ=new IndexMinPQ<>(g.V());
        this.destSPTEdgeTo=new Edge[g.V()];
        this.destSPTDistTo=new int[g.V()];
        this.destSPTPQ=new IndexMinPQ<>(g.V());
        this.thirdSPTDistTo=new int[g.V()];
        this.thirdSPTEdgeTo= new Edge[g.V()];
        this.thirdSPTPQ=new IndexMinPQ<>(g.V());
        this.citiesWithDinner=new HashSet<>();
        for(int v=0;v<g.V();v++){
            sourceSPTDistTo[v]=Integer.MAX_VALUE;
            destSPTDistTo[v]=Integer.MAX_VALUE;
            thirdSPTDistTo[v]=Integer.MAX_VALUE;
            sourceSPTNumNonDinnerPathsToVertex[v]=1;
        }
    }

    /** Defines a highway leading (bi-directionally) between two cities, of
     * specified duration.
     *
     * @param city1 identifies a 1 <= city <= n, must differ from city2
     * @param city2 identifies a 1 <= city <= n, must differ from city1
     * @param duration the bi-directional duration of a trip between the two
     * cities on this highway, must be non-negative
     */
    public void addHighway(final int city1, final int duration, final int city2) {
        if(city1<1||city1>g.V()+1||city2<1||city2>g.V()+1||city1==city2||duration<0){
            throw new IllegalArgumentException("problem with inputs");
        }
        Edge e=new Edge(city1-1,city2-1,duration);
        this.g.addEdge(e);
    }

    /** Specifies that a minyan can be found in the specified city.
     *
     * @param city identifies a 1 <= city <= n
     */
    public void hasDinner(final int city) {
        if(city<1||city>this.g.V()+1){
            throw new IllegalArgumentException("problem with city number");
        }
        this.citiesWithDinner.add(city-1);
    }

    private void performDijkstra(){
        destSPTPQ.insert(this.g.V()-1,0);
        destSPTDistTo[this.g.V()-1]=0;
        while(!destSPTPQ.isEmpty()){
            destRelax(this.g,destSPTPQ.delMin());
        }
        sourceSPTPQ.insert(0,0);
        sourceSPTDistTo[0]=0;
        while(!sourceSPTPQ.isEmpty()){
            sourceRelax(this.g, sourceSPTPQ.delMin());
        }
        if(this.sourceSPTNumYesDinnerPathsToVertex[this.g.V()-1]==0){
            this.sourceSPTNumYesDinnerPathsToVertex[this.g.V()-1]=-1;
        }
        for(Integer i:this.citiesWithDinner){
            int sum=sourceSPTDistTo[i]+destSPTDistTo[i];
            if(sum<lengthOfShortestPath){
                lengthOfShortestPath=sum;
            }
        }
        //final dijkstra
        thirdSPTPQ.insert(this.g.V()-1,0);
        thirdSPTDistTo[this.g.V()-1]=0;
        while(!thirdSPTPQ.isEmpty()){
            int min=thirdSPTPQ.delMin();
            if(this.sourceSPTNumYesDinnerPathsToVertex[min]!=-1&&(this.sourceSPTDistTo[min]+this.destSPTDistTo[min]==this.lengthOfShortestPath)){
                this.numShortestPathsWithDinner+=this.sourceSPTNumYesDinnerPathsToVertex[min];
            }
            thirdSPTRelax(this.g,min);
        }
    }
    private void sourceRelax(UndirectedEdgeWeightedGraph g, int v){
        for(Edge e: g.adj(v)){
            int w=e.other(v);
            int wDistFromSource=sourceSPTDistTo[w];
            int vDistFromSource=sourceSPTDistTo[v];
            int wDistFromDest=destSPTDistTo[w];
            int vDistFromDest=destSPTDistTo[v];
            int nonDinnerPathsToV=sourceSPTNumNonDinnerPathsToVertex[v];
            int yesDinnerPathsToV=sourceSPTNumYesDinnerPathsToVertex[v];
            boolean relevant=wDistFromDest<vDistFromDest||yesDinnerPathsToV==0;
            if(wDistFromSource>vDistFromSource+e.weight()){
                sourceSPTDistTo[w]=vDistFromSource+e.weight();
                sourceSPTEdgeTo[w]=e;
                sourceSPTNumNonDinnerPathsToVertex[w]=nonDinnerPathsToV;
                if(this.citiesWithDinner.contains(w)&&(relevant)) {
                    sourceSPTNumYesDinnerPathsToVertex[w] = sourceSPTNumNonDinnerPathsToVertex[w];
                    this.shiftedNumberOfDinnerPathsAwayFromThisVertex = true;
                }
                else if (relevant) {
                    sourceSPTNumYesDinnerPathsToVertex[w] = yesDinnerPathsToV;
                    this.shiftedNumberOfDinnerPathsAwayFromThisVertex = true;
                }
                if(sourceSPTPQ.contains(w)) sourceSPTPQ.changeKey(w,sourceSPTDistTo[w]);
                else sourceSPTPQ.insert(w,sourceSPTDistTo[w]);
            }
            else if(wDistFromSource==vDistFromSource+e.weight()){
                sourceSPTNumNonDinnerPathsToVertex[w]+=nonDinnerPathsToV;
                if(this.citiesWithDinner.contains(w)&&(relevant)) {
                    sourceSPTNumYesDinnerPathsToVertex[w] += nonDinnerPathsToV;
                    shiftedNumberOfDinnerPathsAwayFromThisVertex = true;
                }
                else if(relevant) {
                    sourceSPTNumYesDinnerPathsToVertex[w] += yesDinnerPathsToV;
                    this.shiftedNumberOfDinnerPathsAwayFromThisVertex = true;
                }
            }
        }
        //this line is new
        if(shiftedNumberOfDinnerPathsAwayFromThisVertex){
            this.sourceSPTNumYesDinnerPathsToVertex[v]=-1;
        }
        shiftedNumberOfDinnerPathsAwayFromThisVertex=false;
    }
    private void destRelax(UndirectedEdgeWeightedGraph g, int v){
        for(Edge e: g.adj(v)){
            int w=e.other(v);
            if(destSPTDistTo[w]>destSPTDistTo[v]+e.weight()){
                destSPTDistTo[w]=destSPTDistTo[v]+e.weight();
                destSPTEdgeTo[w]=e;
                if(destSPTPQ.contains(w)) destSPTPQ.changeKey(w,destSPTDistTo[w]);
                else destSPTPQ.insert(w,destSPTDistTo[w]);
            }
        }
    }
    private void thirdSPTRelax(UndirectedEdgeWeightedGraph g, int v){
        for(Edge e: g.adj(v)){
            int w=e.other(v);
            if(thirdSPTDistTo[w]>thirdSPTDistTo[v]+e.weight()){
                thirdSPTDistTo[w]=thirdSPTDistTo[v]+e.weight();
                thirdSPTEdgeTo[w]=e;
                if(thirdSPTPQ.contains(w)) thirdSPTPQ.changeKey(w,thirdSPTDistTo[w]);
                else thirdSPTPQ.insert(w,thirdSPTDistTo[w]);
            }
        }
    }
    //helper methods based on Sedgewick p649
    public boolean sourceHasPathTo(int v){
        return sourceSPTDistTo[v]<Integer.MAX_VALUE;
    }
    public boolean destHasPathTo(int v){
        return destSPTDistTo[v]<Integer.MAX_VALUE;
    }
    public Iterable<Edge> sourcePathTo(int v){
        if(!sourceHasPathTo(v)) return null;
        Stack<Edge> pathTo=new Stack<>();
        Edge e=sourceSPTEdgeTo[v];
        int toVertex=v;
        int fromVertex=0;
        while(e!=null){
            pathTo.push(e);
            fromVertex=e.other(toVertex);
            e=sourceSPTEdgeTo[fromVertex];
            toVertex=fromVertex;
        }
        return pathTo;
    }
    public Iterable<Edge> destPathTo(int v){
        if(!destHasPathTo(v)) return null;
        Stack<Edge> pathTo=new Stack<>();
        Edge e=destSPTEdgeTo[v];
        int toVertex=v;
        int fromVertex=0;
        while(e!=null){
            pathTo.push(e);
            fromVertex=e.other(toVertex);
            e=destSPTEdgeTo[fromVertex];
            toVertex=fromVertex;
        }
        return pathTo;
    }
    /** Find a solution to the FindDinner problem based on state specified by the
     * constructor, addHighway(), and hasDinner() API.  Clients access the
     * solution through the shortestDuration() and nShortestDurationTrips() APIs.
     */
    public void solveIt() {
        invokedSolveIt=true;
        performDijkstra();
        //printStuff();
        //deal with results
    }
    /** Returns the duration of the shortest trip satisfying the FindDinner
     * constraints.
     *
     * @return duration of the shortest trip, undefined if client hasn't
     * previously invoked solveIt().
     */
    public int shortestDuration() {
        if(!invokedSolveIt){
            throw new IllegalStateException("solveIt hasn't been invoked yet");
        }
        return this.lengthOfShortestPath;
    }

    /** Returns the number of distinct trips that satisfy the FindDinner
     * constraints.
     *
     * @return number of shortest duration trips, undefined if client hasn't
     * previously invoked solveIt()..
     */
    public int numberOfShortestTrips() {
        if(!invokedSolveIt){
            throw new IllegalStateException("solveIt hasn't been invoked yet");
        }
        if(this.citiesWithDinner.size()!=0&&this.sourceSPTNumYesDinnerPathsToVertex[this.g.V()-1]==-1){
            return this.numShortestPathsWithDinner;
        }
        return this.sourceSPTNumYesDinnerPathsToVertex[this.g.V()-1];
    }

} // FindDinner

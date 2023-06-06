package edu.yu.da;
import java.lang.*;
import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;

public class WeAreAllConnected extends WeAreAllConnectedBase{
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
            if(pq[i]<0||pq[j]<0) return false;
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
    public static class Segment extends SegmentBase{
        public final int x,y,duration;
        /**
         * Constructor.
         *
         * @param x        one end of a communication segment, specified by a city id
         *                 (0..n-1)
         * @param y        one end of a communication segment, specified by a city id
         *                 (0..n-1).  You may assume that "x" differs from "y".
         * @param duration unit-less amount of time required for a message to
         *                 travel from either end of the segment to the other.  You may assume that
         */
        public Segment(int x, int y, int duration) {
            super(x, y, duration);
            this.x=x;
            this.y=y;
            this.duration=duration;
        }
        public int getX(){return this.x;}
        public int getY(){return this.y;}
        public int getDuration(){return this.duration;}
        @Override
        public boolean equals(Object o){
            if(this.getClass()!=o.getClass()) return false;
            Segment other=(Segment)o;
            if(this.x!=other.x||this.y!=other.y||this.duration!=other.duration) return false;
            return true;
        }
        @Override
        public int hashCode(){
            Integer myX=this.x;
            Integer myY=this.y;
            Integer myDuration=this.duration;
            return myX.hashCode()+myY.hashCode()+myDuration.hashCode();
        }
    }
    class Edge{
        private int v;
        private int w;
        private int weight;
        public Edge(int v,int w,int weight){
            this.v=v;
            this.w=w;
            this.weight=weight;
        }
        public int either(){return this.v;}
        public int other(int v){
            if(v==this.v) return this.w;
            if(v==this.w)return this.v;
            else throw new IllegalArgumentException("vertex doesn't belong to this edge");
        }
        public int getWeight(){return this.weight;}
    }
    class WeightedUndirectedGraph{
        private int V;
        private List<Edge>[] adj;
        public WeightedUndirectedGraph(int n){
            this.V=n;
            this.adj=(List<Edge>[]) new List[n];
            for(int i=0;i<n;i++){
                adj[i]=new ArrayList<Edge>();
            }
        }
        public int getV(){return this.V;}
        public void addEdge(Edge e){
            int v=e.either(), w=e.other(v);
            this.adj[v].add(e);
            this.adj[w].add(e);
        }
        public Iterable<Edge> adj(int v){return this.adj[v];}
    }
    private int[][] distances;
    public WeightedUndirectedGraph g;
    private SegmentBase currentSolution;
    private int currentSolutionLowersBy=Integer.MIN_VALUE;
    private int n;
    private Edge[] edgeTo;
    private int[] distTo;
    private IndexMinPQ<Integer> pq;
    public WeAreAllConnected(){
        super();
    }
    @Override
    public SegmentBase findBest(int n, List<SegmentBase> current, List<SegmentBase> possibilities) {
        this.distances = new int[n][n];
        this.edgeTo=new Edge[n];
        this.distTo=new int[n];
        this.g=new WeightedUndirectedGraph(n);
        this.n = n;
        for (SegmentBase sb : current) {
            Edge e=new Edge(sb.x,sb.y,sb.duration);
            g.addEdge(e);
        }
        this.preProcessDistances();
        for (SegmentBase sb : possibilities) {
            this.checkPossibility(sb);
        }
        return this.currentSolution;
    }
    private void preProcessDistances(){
        for(int i=0;i<n;i++){
            calculateShortestDistances(i);
        }
    }
    private void calculateShortestDistances(int source){
        this.distTo=new int[this.n];
        this.edgeTo=new Edge[n];
        this.pq=new IndexMinPQ<>(n);
        for(int v=0;v<this.n;v++){
            distTo[v]=Integer.MAX_VALUE;
        }
        distTo[source]=0;
        pq.insert(source,0);
        while(!pq.isEmpty()){
            relax(this.g,pq.delMin());
        }
        //now use distTo to add shortest distances to the matrix
        for(int i=0;i<n;i++){
            distances[source][i]=distTo[i];
        }
    }
    private void relax(WeightedUndirectedGraph g,int v){
        for(Edge e:g.adj(v)){
            int w=e.other(v);
            if(distTo[w]>distTo[v]+e.getWeight()){
                distTo[w]=distTo[v]+e.getWeight();
                edgeTo[w]=e;
                if(pq.contains(w)) pq.changeKey(w,distTo[w]);
                else pq.insert(w,distTo[w]);
            }
        }
    }
    private void checkPossibility(SegmentBase sb){
        int myTotalShortened=0;
        int v1=sb.x;
        int v2=sb.y;
        int length=sb.duration;
        for(int i=0;i<this.n;i++){
            for(int j=i;j<n;j++){
                double currentDistance=distances[i][j];
                if(distances[i][v1]+distances[v2][j]+length<currentDistance){
                    myTotalShortened+=currentDistance-(distances[i][v1]+distances[v2][j]+length);
                    currentDistance=distances[i][v1]+distances[v2][j]+length;
                }
                if(distances[i][v2]+distances[v1][j]+length<currentDistance){
                    myTotalShortened+=currentDistance-(distances[i][v2]+distances[v1][j]+length);
                }
            }
        }
        if(myTotalShortened>this.currentSolutionLowersBy){
            this.currentSolutionLowersBy=myTotalShortened;
            this.currentSolution=sb;
        }
    }
}

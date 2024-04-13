package edu.utdallas.s3.vsa.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

//import edu.utdallas.s3.vsa.backwardslicing.DataSourceType;

public interface IDGNode {

	public Set<IDGNode> getDependents();
	
	public Set<IDGNode> getDirectAndIndirectDependents(Set<IDGNode> ret);

	public int getUnsovledDependentsCount();

	public boolean hasSolved();

	public void solve();

	public boolean canBePartiallySolve();

	public void initIfHavenot();

	public boolean inited();

	//public HashSet<DataSourceType> getDataSrcs();
	
	public ArrayList<HashMap<Integer, HashSet<String>>> getResult();
}

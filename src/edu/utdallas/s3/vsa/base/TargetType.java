package edu.utdallas.s3.vsa.base;

public enum TargetType {
	RIGHTPART(-1),BASEOBJECT(-2);
	int tid;
	private TargetType(int id){
		tid = id;
	}
	
	public int getType(){
		return tid;
	}
}

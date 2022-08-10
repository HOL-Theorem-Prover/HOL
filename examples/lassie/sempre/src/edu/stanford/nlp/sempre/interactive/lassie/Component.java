package edu.stanford.nlp.sempre.interactive.lassie;

import java.util.Set;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.stanford.nlp.sempre.interactive.Item;


// Individual items with some properties
public class Component extends Item {
    public Set<String> names;
    public Map<String,List<String>> features;
   
    public Component(Set<String> names, Map<String,List<String>> features) {
	this.names = names;
	this.features = features;
    }
    
    public Component(String name, Map<String,List<String>> features) {
	this.names = new HashSet<String>();
	names.add(name);
	this.features = features;
    }
    
    public boolean selected() { return false; } // explicit global selection
    public void select(boolean sel) {};
    public void update(String rel, Object value) {};
    
    public Object get(String feature) {
	return this.features.get(feature);
    }
}

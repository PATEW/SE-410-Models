public class Resource {
    private String type;
    private boolean isTaken = false;

    public Resource(String type) {
        this.type = type;
    }

    public String getType() {
        return this.type;
    }

    public boolean isTaken() {
        return this.isTaken;
    }

    public synchronized void takeResource() {
        this.isTaken = true;
    }

    public synchronized void releaseResource() {
        this.isTaken = false;
    }
}


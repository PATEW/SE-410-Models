public class Main {
    public static void main(String[] args) {
        Resource RA_1 = new Resource("A");
        Resource RA_2 = new Resource("A");

        Resource RB_1 = new Resource("B");
        Resource RB_2 = new Resource("B");

        Process p1 = new Process(RA_1, RA_2, RB_1, RB_2);
        Process p2 = new Process(RA_1, RA_2, RB_1, RB_2);
        Process p3 = new Process(RA_1, RA_2, RB_1, RB_2);
        Process p4 = new Process(RA_1, RA_2, RB_1, RB_2);
        Process p5 = new Process(RA_1, RA_2, RB_1, RB_2);
        Process p6 = new Process(RA_1, RA_2, RB_1, RB_2);

        p1.start();
        p2.start();
        p3.start();
        p4.start();
        p5.start();
        p6.start();
    }
}

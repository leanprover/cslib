/-
Interesting in several ways:
- It's probabilisitcally complete.
  - I'd like to prove not only that it's probabilistically complete, but also a bound. The standard argument is based on obstacle-free balls of radius `ε` along a path from `start` to `goal` with clearance `ε` and then computing the probability that at least one ball has no sampled configurations within it.
- For the easiest proof, `get_neighbors` can return all points. A more efficient implementation can use the closest `k = log n` points.
-/


/-
function get_neighbors(c: Configuration) returns (neighbors: [Configuration]);

function can_connect(c1: Configuration, c2: Configuration) returns (result: bool);

procedure Roadmap.add(c: Configuration)
{

  var i: int;
  var n: Configuration;

  i := 0;
  call add_vertex(c);
  call neighbors := get_neighbors(c);

  while (i < |neighbors|)
  {
    n := neighbors[i];
    call result := can_connect(c, n);
    if (result) {
      call add_edge(c, n);
    }
    i := i + 1;
  }
}

procedure PRMLite(start: Configuration, goal: Configuration, c_space: ConfigurationSpace) returns (path: [Configuration])
{
  var roadmap: RoadMap;
  var c: Configuration;
  var collision_free: bool;
  var connected: bool;

  call roadmap := RoadMap(c_space);
  call roadmap.add(start);
  call roadmap.add(goal);

  while (true)
  {
    call c := sample_configuration();
    call collision_free := c_space.in_collision(c);
    collision_free := !collision_free;

    if (collision_free) {
      call roadmap.add(c);

      call connected := roadmap.connected(start, goal);
      if (connected) {
        call path := roadmap.shortest_path(start, goal);
        return;
      }
    }
  }
}
-/

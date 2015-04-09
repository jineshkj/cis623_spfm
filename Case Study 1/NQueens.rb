#!/usr/bin/env ruby

# default to a 4x4 chess board
$N =
  if ARGV[0] then
    ARGV[0].to_i
  else
    4
  end

# ensure we have a minimum of 4x4 chess board
if $N < 4 then
  puts "N must be greater than or equal to 4"
  exit 1
end

# determine position number from row and col
def pos(row, col, n)
  if col > 0 and col <= n then
    if row > 0 and row <= n then
      return (((row - 1) * n) + col)
    end
  end
  
  return nil
end

# determine the horizontal, vertical and diagonal
# conflicting positions on board
def conflicting(p, n)
  row = ((p - 1) / n) + 1
  col = ((p - 1) % n) + 1
  con = []
  
  1.upto(n) do |d|
    # items in same row
    con << pos(row, col - d, n)
    con << pos(row, col + d, n)
    
    # items in same col
    con << pos(row - d, col, n)
    con << pos(row + d, col, n)

    # items in diagonal
    con << pos(row - d, col - d, n)
    con << pos(row + d, col - d, n)
    con << pos(row - d, col + d, n)
    con << pos(row + d, col + d, n)
  end
    
  con.delete nil
  con
end

# generate constraint 1
def constraint_1(n)
  pos = 0
  clauses = []
  
  n.times do
    clause = []
    n.times do
      clause << (pos += 1)
    end
    clauses << clause
  end
  
  clauses
end

# generate constraint 2
def constraint_2(n)
  clauses = []
  
  # iterate for all positions on the board
  1.upto(n * n) do |p|
    conflicting(p, n).each do |con|
      # eliminate duplicate entries by ignoring conflicts with
      # positions we have already considered before
      if con > p then
        clauses << [-p, -con]
      end
    end
  end
  
  clauses
end

# combine the two constraint to form final cnf expr
clauses = constraint_1($N) + constraint_2($N)

# print the cnf source for SAT4J SAT solver
puts "p cnf #{$N*$N} #{clauses.size}"
clauses.each do |clause|
  puts "#{clause.join(' ') } 0"
end

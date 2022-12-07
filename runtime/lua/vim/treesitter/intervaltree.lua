-- If you are given a range like { 0, 0, 0, 4 }, you can pass this around to
-- any child LanguageTrees easily. But if you have used a region like the one marked with
-- xs below...
-- 
-- /// xxxxxxxx
-- /// xxxx
-- /// xxxxxxxxxxx
--
-- ... then when your child LanguageTree returns its injection query matches,
-- if those matches are multi-line matches (like a fenced code block in markdown),
-- then they will clobber the starts of lines. You'll get a region like so:
-- 
-- /// xxxxxxxx
-- xxxxxxxx
-- xxxxxxxxxxxxxxx
--
-- And hence any 3rd-level child parsers of that one will be working in a range
-- with some extra comment marks or whatever it is in the middle of it.
--
-- So we have to be careful to split up any ranges when passing them to a child
-- LanguageTree. This file implements that. Entry point is RangeTree:clip_region().

---@class IPoint
---@field point number
---@field range any

---@alias Range6 number[]

---@class IntervalTree
---@field root IntervalNode
---@field get_range_fn fun(x: any): number, number
---@field sorted_points IPoint[]
local IntervalTree = {}
IntervalTree.__index = IntervalTree

---@class IntervalNode
---@field centre integer
---@field left IntervalNode?
---@field right IntervalNode?
---@field by_begin_point any[]
---@field by_end_point any[]
---@field min number
---@field max number

---@param region any[]
---@param get_range_fn fun(x: any): number, number
---@return number
---@return number
local function min_max_region(region, get_range_fn)
  local min = nil
  local max = nil
  for _, x in ipairs(region) do
    local from, to = get_range_fn(x)
    if min == nil or from < min then
      min = from
    end
    if max == nil or to > max then
      max = to
    end
  end
  return min, max
end

---@param region any[]
---@param get_range_fn fun(x: any): number, number
---@return IntervalNode?
local function _interval_node_create(region, get_range_fn, by_begin_cmp, by_end_cmp, min, max)
  if #region == 0 then
    return nil
  end
  if min == nil or max == nil then
    min, max = min_max_region(region, get_range_fn)
  end
  local centre = math.floor((min + max) / 2)
  local left_ranges = {}
  local right_ranges = {}
  local overlaps = {}
  for _, range in ipairs(region) do
    local from, to = get_range_fn(range)
    if from > to then
      error("from > to: " .. from .. " > " .. to)
    end
    -- assumes well-formed ranges, i.e. from <= to
    if to < centre then
      table.insert(left_ranges, range)
    elseif from > centre then
      table.insert(right_ranges, range)
    else
      table.insert(overlaps, range)
    end
  end
  local left = _interval_node_create(left_ranges, get_range_fn, by_begin_cmp, by_end_cmp, min, centre)
  local right = _interval_node_create(right_ranges, get_range_fn, by_begin_cmp, by_end_cmp, centre, max)

  ---@type any[]
  local by_begin_point = overlaps
  ---@type any[]
  local by_end_point = vim.tbl_map(function(x)
    return x
  end, by_begin_point)
  table.sort(by_begin_point, by_begin_cmp)
  table.sort(by_end_point, by_end_cmp)
  return {
    centre = centre,
    left = left,
    right = right,
    by_begin_point = by_begin_point,
    by_end_point = by_end_point,
    min = min,
    max = max,
  }
end

local function point_cmp(a, b)
  return a.point < b.point
end

---@param region any[]
---@param get_range_fn fun(x: any): number, number
---@return IntervalTree
local function interval_tree_create(region, get_range_fn)
  -- create these closures once to avoid doing it on every node
  local function by_begin_cmp(a, b)
    local afrom = get_range_fn(a)
    local bfrom = get_range_fn(b)
    return afrom < bfrom
  end

  local function by_end_cmp(a, b)
    local _, ato = get_range_fn(a)
    local _, bto = get_range_fn(b)
    -- reversed sort
    return ato > bto
  end

  local root = _interval_node_create(region, get_range_fn, by_begin_cmp, by_end_cmp)
      or {
        -- ensure root is not nil
        centre = 0,
        left = nil,
        right = nil,
        by_begin_point = {},
        by_end_point = {},
        min = nil,
        max = nil,
      }
  ---@type IPoint[]
  local points = {}
  for _, range in ipairs(region) do
    local from, to = get_range_fn(range)
    table.insert(points, { point = from, range = range })
    if to ~= from then
      table.insert(points, { point = to, range = range })
    end
  end
  table.sort(points, point_cmp)
  return {
    root = root,
    sorted_points = points,
    get_range_fn = get_range_fn,
  }
end

---@param node IntervalNode?
---@param point number
---@param results any[]
---@param get_range_fn fun(x: any): number, number
local function _point_query_inner(node, point, results, get_range_fn, tree_max)
  if node == nil then
    return
  end
  local next_node = nil
  if point == node.centre then
    for _, range in ipairs(node.by_begin_point) do
      local from, to = get_range_fn(range)
      local k = (tree_max * from) + to
      results[k] = range
    end
    return
  elseif point < node.centre then
    next_node = node.left
    for _, range in ipairs(node.by_begin_point) do
      local from, to = get_range_fn(range)
      if from <= point then
        local k = (tree_max * from) + to
        results[k] = range
      else
        break
      end
    end
  elseif point > node.centre then
    next_node = node.right
    for _, range in ipairs(node.by_end_point) do
      local from, to = get_range_fn(range)
      if to >= point then
        local k = (tree_max * from) + to
        results[k] = range
      else
        break
      end
    end
  end
  return _point_query_inner(next_node, point, results, get_range_fn, tree_max)
end

---@param tree IntervalTree
---@param point number
---@return any[]
local function interval_tree_point_query(tree, point)
  local results = {}
  if tree.root.max == nil then
    return results
  end
  _point_query_inner(tree.root, point, results, tree.get_range_fn, tree.root.max)
  return results
end

-- http://lua-users.org/wiki/BinarySearch
-- Avoid heap allocs for performance
local default_fcompval = function(value)
  return value
end
local fcompf = function(a, b)
  return a < b
end
local fcompr = function(a, b)
  return a > b
end

--- Finds values in a _sorted_ list using binary search.
--- If present, returns the range of indices that are == to `value`
--- If absent, returns the insertion point (duplicated), which may go off the end (#t + 1)
---@return integer range start
---@return integer range end
---@return boolean true if value was present
local function binsearch(t, value, fcompval, reversed)
  -- Initialise functions
  fcompval = fcompval or default_fcompval
  local fcomp = reversed and fcompr or fcompf
  --  Initialise numbers
  local iStart, iEnd, iMid = 1, #t, 0
  local iState = 0
  -- Binary Search
  while iStart <= iEnd do
    -- calculate middle
    iMid = math.floor((iStart + iEnd) / 2)
    -- get compare value
    local value2 = fcompval(t[iMid])
    -- get all values that match
    if value == value2 then
      local tfound, num = { iMid, iMid }, iMid - 1
      while num > 0 and value == fcompval(t[num]) do
        tfound[1], num = num, num - 1
      end
      num = iMid + 1
      while num <= #t and value == fcompval(t[num]) do
        tfound[2], num = num, num + 1
      end
      local from, to = unpack(tfound)
      return from, to, true
      -- keep searching
    elseif fcomp(value, value2) then
      iEnd = iMid - 1
      iState = 0
    else
      iStart = iMid + 1
      iState = 1
    end
  end
  -- modified to return the right place for such a value to be inserted, with 'false'
  -- indicating it wasn't in there already
  return iMid + iState, iMid + iState, false
end

-- local list = { 1, 2, 3, 3, 4, 6, 7 }
-- binsearch(list, 3) -- {3, 4, true}
-- binsearch(list, 5) -- {6, 6, false}

---@param ipoint IPoint
---@return integer
local function getpoint(ipoint)
  return ipoint.point
end

---@param tree IntervalTree
---@param from number
---@param to number
---@return any[]
local function interval_tree_interval_query(tree, from, to)
  local min, max = tree.root.min, tree.root.max
  local results = {}
  if min == nil then
    return results
  end

  local istart, _ = binsearch(tree.sorted_points, from, getpoint)
  local _, iend = binsearch(tree.sorted_points, to, getpoint)
  -- insertion may go at the end of the table. we don't want to zoom off the end
  -- when iterating.
  iend = math.min(iend, #tree.sorted_points)
  if istart == nil or iend == nil then
    return results
  end

  local k

  for i = istart, iend do
    local range = tree.sorted_points[i].range
    local f, t = tree.get_range_fn(range)
    k = (max * f) + t
    results[k] = range
  end

  _point_query_inner(tree.root, from, results, tree.get_range_fn, tree.root.max)
  return results
end

-- local region = { {1, 3}, {2, 4}, {5, 9}, {2, 3}, {1, 4}, {6, 9}, {3, 9}, }
-- local interval_tree = IntervalTree.new(region, unpack)
-- interval_tree:containing_point(4) -- { {2, 4}, {1, 4}, {3, 9} }
-- interval_tree:overlapping(3, 7) -- { {1, 3}, {2, 4}, {2, 3}, {1, 4}, {3, 9} }

---@param region any[]
---@param get_range_fn fun(x: any): number, number
---@return IntervalTree
function IntervalTree.new(region, get_range_fn)
  if region == nil then error("region was nil in IntervalTree.new") end
  return setmetatable(interval_tree_create(region, get_range_fn), IntervalTree)
end

--- Iterate the result set using pairs, as it will be very sparse.
---@param point integer
---@return Range6[]
function IntervalTree:containing_point(point)
  return interval_tree_point_query(self, point)
end

--- Iterate the result set using pairs, as it will be very sparse.
---@param from integer
---@param to integer
---@return any[]
function IntervalTree:overlapping_interval(from, to)
  return interval_tree_interval_query(self, from, to)
end

--- Iterate the result set using pairs, as it will be very sparse.
---@return boolean
function IntervalTree:is_empty()
  return #self.sorted_points == 0
end

---@class RangeTree
---@field interval_tree IntervalTree
local RangeTree = {}
RangeTree.__index = RangeTree

---@param range Range6
---@return integer
---@return integer
local function range_bytes(range)
  return range[3], range[6]
end

---@return RangeTree
function RangeTree.new(region)
  return setmetatable({
    interval_tree = IntervalTree.new(region, range_bytes),
  }, RangeTree)
end

--- Iterate the result set using pairs, as it will be very sparse.
---@param point integer
---@return Range6[]
function RangeTree:containing_point(point)
  return self.interval_tree:containing_point(point)
end

--- Iterate the result set using pairs, as it will be very sparse.
---@param from integer
---@param to integer
---@return Range6[]
function RangeTree:overlapping_interval(from, to)
  return self.interval_tree:overlapping_interval(from, to)
end

--- Iterate the result set using pairs, as it will be very sparse.
---@param range Range6
---@return Range6[]
function RangeTree:overlapping_range6(range)
  local from, to = range_bytes(range)
  return self:overlapping_interval(from, to)
end

-- This is the idea:
-- parent: xxxxxx    xxxx  xxxxx
-- child:    ----------------
-- result:   oooo    iiii  oo

--- Sort the 
---@param a Range6
---@param b Range6
local function overlap_cmp(a, b)
  local af, at = range_bytes(a)
  local bf, bt = range_bytes(b)
  if af < bf then
    return true
  elseif at < bt then
    return true
  else
    return false
  end
end

---@param dst Range6
---@param src Range6
local function copy_start(dst, src)
  dst[1] = src[1]
  dst[2] = src[2]
  dst[3] = src[3]
end

---@param dst Range6
---@param src Range6
local function copy_end(dst, src)
  dst[4] = src[4]
  dst[5] = src[5]
  dst[6] = src[6]
end

---@return Range6[]
function RangeTree:clip_range(child)
  local child_from, child_to = self.interval_tree.get_range_fn(child)
  local results = {}
  local overlapping = self:overlapping_interval(child_from, child_to)

  local o2 = {}
  for _, r in pairs(overlapping) do
    table.insert(o2, r)
  end
  table.sort(o2, overlap_cmp)
  overlapping = o2

  local last_f, last_t, last_r, coalesced
  if #overlapping == 0 then
    return results
  end

  last_f, last_t = range_bytes(overlapping[1])
  last_r = { unpack(overlapping[1]) }
  coalesced = {}

  if #overlapping > 1 then
    for i = 2, #overlapping do
      local r = overlapping[i]
      local f, t = range_bytes(r)
      if f <= last_f and t >= last_f then
        -- expand the previous range backwards
        copy_start(last_r, r)
        if t > last_t then
          -- we cover the previous range entirely
          copy_end(last_r, r)
        end
      elseif f >= last_f and f <= last_t and t > last_t then
        -- expand the previous range forwards
        copy_end(last_r, r)
      else
        table.insert(coalesced, last_r)
        last_r = { unpack(r) }
      end
    end
  end
  table.insert(coalesced, last_r)

  for _, parent in ipairs(coalesced) do
    -- remove at some point
    parent = { unpack(parent) }
    -- this would be a zero length range
    if parent[3] >= parent[6] then
      goto continue
    end

    -- parent: xxxxxx    xxxxxxxx
    -- child:    ------    ----
    -- result:   oooo      oooo
    if parent[3] < child_from then
      copy_start(parent, child)
    end

    -- parent:   xxxxxx  xxxxxxxx
    -- child:  ------      ----
    -- result:   oooo      oooo
    if parent[6] > child_to then
      copy_end(parent, child)
    end
    -- this would be a zero length range
    if parent[3] >= parent[6] then
      goto continue
    end
    -- if not modified by previous rules, then it's just wholly contained
    -- parent:   xxxxxx
    -- child:  -----------
    -- result:   iiiiii
    table.insert(results, parent)
    ::continue::
  end

  return results
end

function RangeTree:clip_region(region)
  if region == nil then
    return {}
  end
  if self.interval_tree:is_empty() then
    return region
  end
  local results = {}
  for _, range in ipairs(region) do
    for _, clipped in ipairs(self:clip_range(range)) do
      local from, to = range_bytes(clipped)
      if from > to then
        error("from > to: " .. from .. " > " .. to)
      end
      table.insert(results, clipped)
    end
  end
  return results
end

return {
  RangeTree = RangeTree,
  IntervalTree = IntervalTree,
}
